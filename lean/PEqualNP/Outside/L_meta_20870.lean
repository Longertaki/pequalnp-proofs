import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20870 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31361057 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 18]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
