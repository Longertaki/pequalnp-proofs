import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21948 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33585 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [11, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 8]⟩], 14⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
