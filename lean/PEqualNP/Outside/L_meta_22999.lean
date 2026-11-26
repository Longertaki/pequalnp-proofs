import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22999 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34074 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩], 12⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
