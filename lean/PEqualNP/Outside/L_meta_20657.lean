import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20657 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (12682240 : ℕ).testBit (5 * u.val + v.val)) 7 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 11]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
