import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21983 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16782 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [5, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
