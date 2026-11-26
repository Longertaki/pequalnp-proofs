import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22193 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17046 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [12, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 15]⟩], 17⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
