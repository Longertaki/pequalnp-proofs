import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21525 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (291807 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 8]⟩], 9⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
