import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22220 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17950 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [13, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 16]⟩], 17⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
