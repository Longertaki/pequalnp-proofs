import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20863 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (30280737 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 16]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
