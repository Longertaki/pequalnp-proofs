import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21575 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (17052255 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9, 2]⟩], 10⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
