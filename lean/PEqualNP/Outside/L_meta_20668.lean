import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20668 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (16223232 : ℕ).testBit (5 * u.val + v.val)) 7 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
