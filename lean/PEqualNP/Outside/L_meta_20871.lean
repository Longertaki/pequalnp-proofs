import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20871 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31388737 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 17]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 18]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
