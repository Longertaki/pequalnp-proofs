import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20639 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7372800 : ℕ).testBit (5 * u.val + v.val)) 5 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 10]⟩], 14⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
