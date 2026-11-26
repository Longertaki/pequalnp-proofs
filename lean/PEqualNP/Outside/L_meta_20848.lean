import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20848 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (21366817 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 16]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 13]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
