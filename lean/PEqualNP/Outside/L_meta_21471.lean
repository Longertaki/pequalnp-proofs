import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21471 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8862 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩], 13⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
