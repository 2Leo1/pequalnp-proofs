import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19067_aux
open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.and, [2, 4]⟩, ⟨.not, [6]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 11]⟩,
    ⟨.or, [10, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_19067_aux

theorem PEqualNP.Outside.L_meta_19067 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (363 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19067_aux.witness, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_19067_aux.witness, List.mem_cons, List.not_mem_nil,
    or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
