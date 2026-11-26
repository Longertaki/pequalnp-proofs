import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21938 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33598 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 14]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
