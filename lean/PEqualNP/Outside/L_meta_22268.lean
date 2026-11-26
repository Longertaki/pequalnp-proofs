import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22268 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20157 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [11, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [16, 15]⟩], 17⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
