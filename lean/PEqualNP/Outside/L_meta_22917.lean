import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22917 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (9116 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 8]⟩], 10⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
