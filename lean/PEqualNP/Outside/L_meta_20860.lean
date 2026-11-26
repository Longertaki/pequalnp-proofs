import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20860 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (27465761 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 16]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 18]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
