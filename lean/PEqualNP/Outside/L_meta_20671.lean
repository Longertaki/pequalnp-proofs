import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20671 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (26443776 : ℕ).testBit (5 * u.val + v.val)) 7 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 15]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
