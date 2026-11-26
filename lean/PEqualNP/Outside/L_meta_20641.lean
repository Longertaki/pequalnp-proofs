import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20641 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32505856 : ℕ).testBit (5 * u.val + v.val)) 5 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 10]⟩], 14⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
