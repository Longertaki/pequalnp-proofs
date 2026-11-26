import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23030 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36156 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 9]⟩], 13⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
