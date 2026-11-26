import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22062 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33968 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [12, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 11]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
