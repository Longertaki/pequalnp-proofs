import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20869 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31354945 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 18]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
