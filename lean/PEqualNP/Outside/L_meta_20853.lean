import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20853 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (26417185 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 16]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 18]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
