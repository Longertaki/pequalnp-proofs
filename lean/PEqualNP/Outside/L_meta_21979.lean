import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21979 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16520 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [12, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 14]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
