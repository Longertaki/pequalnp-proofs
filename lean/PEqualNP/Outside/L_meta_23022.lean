import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23022 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34106 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩], 13⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
