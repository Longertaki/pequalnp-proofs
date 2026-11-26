import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23256 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147216 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [7, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [10, 6]⟩], 11⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
