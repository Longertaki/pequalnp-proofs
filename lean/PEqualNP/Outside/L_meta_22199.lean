import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22199 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17304 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [7, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 16]⟩], 17⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
