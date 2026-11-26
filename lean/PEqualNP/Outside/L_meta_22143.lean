import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22143 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33965 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [14, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 15]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
