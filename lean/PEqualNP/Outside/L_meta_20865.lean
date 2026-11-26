import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20865 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (30280801 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 17]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 18]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
