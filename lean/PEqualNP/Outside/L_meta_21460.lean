import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21460 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (414 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩], 11⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
