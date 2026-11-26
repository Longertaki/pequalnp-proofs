import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22001 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17182 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
