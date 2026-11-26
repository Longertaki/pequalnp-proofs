import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20652 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (6390784 : ℕ).testBit (5 * u.val + v.val)) 7 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 15]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
