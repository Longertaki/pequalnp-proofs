import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20864 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (30280769 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 16]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 18]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
