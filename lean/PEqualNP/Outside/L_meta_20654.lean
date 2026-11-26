import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20654 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7439360 : ℕ).testBit (5 * u.val + v.val)) 7 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
