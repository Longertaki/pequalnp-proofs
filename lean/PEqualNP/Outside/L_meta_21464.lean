import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21464 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (25503 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 10]⟩], 11⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
