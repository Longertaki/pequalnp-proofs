import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21994 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17045 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [13, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 14]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
