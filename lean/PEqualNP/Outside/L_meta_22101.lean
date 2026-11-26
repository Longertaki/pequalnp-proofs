import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22101 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17214 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [1, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
