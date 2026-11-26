import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21999 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17176 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [12, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 10]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
