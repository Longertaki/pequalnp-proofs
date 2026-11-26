import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20859 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (27460641 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 17]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
