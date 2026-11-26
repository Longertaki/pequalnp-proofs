import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20880 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32442401 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 17]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 13]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
