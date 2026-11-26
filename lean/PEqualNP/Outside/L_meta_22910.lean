import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22910 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (399 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 10]⟩], 11⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
