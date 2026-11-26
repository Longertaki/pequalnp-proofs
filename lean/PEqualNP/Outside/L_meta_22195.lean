import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22195 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17077 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [11, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [14, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 13]⟩], 17⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
