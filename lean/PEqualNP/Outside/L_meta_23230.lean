import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23230 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50102 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [7, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩], 11⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
