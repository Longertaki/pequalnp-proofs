import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20647 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (11763712 : ℕ).testBit (5 * u.val + v.val)) 6 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
