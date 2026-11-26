import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_22406

private def witness : Circuit :=
  ⟨[⟨.or, [6, 7]⟩,
    ⟨.or, [0, 2]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [11, 12]⟩,
    ⟨.or, [0, 1]⟩, ⟨.and, [14, 9]⟩,
    ⟨.or, [4, 10]⟩, ⟨.and, [1, 16]⟩,
    ⟨.or, [4, 5]⟩, ⟨.and, [3, 18]⟩,
    ⟨.or, [13, 15]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [20, 21]⟩], 22⟩

private lemma witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst g <;> simp

end PEqualNP.Outside.L_meta_22406

theorem PEqualNP.Outside.L_meta_22406 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (904060 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨L_meta_22406.witness, L_meta_22406.witness_mono, by decide +kernel, by decide +kernel⟩
