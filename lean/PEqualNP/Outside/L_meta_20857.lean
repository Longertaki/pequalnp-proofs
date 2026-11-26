import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20857 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (27039937 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 18]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
