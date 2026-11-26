import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22090 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17051 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [12, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [5, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 14]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
