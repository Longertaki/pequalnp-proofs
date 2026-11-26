import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21943 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18335 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 12]⟩], 14⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
