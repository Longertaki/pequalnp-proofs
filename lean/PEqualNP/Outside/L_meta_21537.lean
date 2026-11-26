import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21537 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (219 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [2, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [5, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 8]⟩], 10⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
