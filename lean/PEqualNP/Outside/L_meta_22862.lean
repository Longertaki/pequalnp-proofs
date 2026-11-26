import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22862 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270583743 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 0]⟩], 10⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
