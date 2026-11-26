import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20851 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (26347553 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 16]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 17]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
