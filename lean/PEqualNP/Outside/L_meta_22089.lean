import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22089 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17033 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [14, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 15]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
