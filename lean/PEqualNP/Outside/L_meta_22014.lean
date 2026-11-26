import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22014 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18223 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [6, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [5, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 14]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
