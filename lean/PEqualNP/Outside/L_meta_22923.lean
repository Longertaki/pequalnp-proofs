import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22923 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8862 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩], 11⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
