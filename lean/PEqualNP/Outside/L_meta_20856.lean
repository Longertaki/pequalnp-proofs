import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20856 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (27037761 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 17]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 13]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
