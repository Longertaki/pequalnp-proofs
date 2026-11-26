import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23386 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (116415 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [5, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [10, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 9]⟩], 12⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
