import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20676 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (9604096 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
