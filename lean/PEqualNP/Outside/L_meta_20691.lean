import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20691 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15762464 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 16]⟩], 17⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
