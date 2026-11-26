import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21470 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8606 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 9]⟩], 13⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
