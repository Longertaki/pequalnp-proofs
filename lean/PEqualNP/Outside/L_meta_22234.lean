import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22234 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17979 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [6, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [14, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 15]⟩], 17⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
