import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22178 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16947 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [14, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 16]⟩], 17⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
