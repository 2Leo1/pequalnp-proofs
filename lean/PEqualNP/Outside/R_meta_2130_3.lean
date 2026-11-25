import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2130_3 :
  ((∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C → (C.wires (List.replicate n Bool.false)).getD C.output Bool.false = Bool.false → ∀ (x11 : Fin C.size), (C.wires (List.replicate n Bool.false)).getD (n + ↑x11) Bool.false = Bool.false)) →
  (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (2 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →             (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) →               ( ∀ (x11 : Fin x5.size), (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x11) Bool.false = Bool.false) → ( ∃ (x11 : PEqualNP.CircuitLowerBounds.Gate), x11 ∈ x5.gates ∧ x11.op.eval [] = Bool.true ∧ x11.inputs.length = (2 : ℕ) ∧ (x11.inputs.all fun (x12 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x12 (0 : ℕ))) = Bool.true) → have x12 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => if x12.op.eval [] = Bool.true ∧ x12.inputs.length = (2 : ℕ) ∧ (x12.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x12) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };               have x13 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x13 x14 : Fin x2) (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x13 ∨ x15 = Fin.natAdd x2 x14);               ∀ (x14 : Fin x2 → Finset (Fin x2)), (∀ (x15 x16 : Fin x2), x16 ∈ x14 x15 → x3 x16 x15 ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (x13 x16 x15) = Bool.true ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x12 (x13 x16 x15) = Bool.false) → ∑ x16 : Fin x2, (x14 x16).card ≤ (44 : ℕ) * Fintype.card { x16 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x16) Bool.false = Bool.false ∧ ∃ (x17 : Fin x2), ∃ x18 ∈ x14 x17, (x5.wires (List.ofFn (x13 x18 x17))).getD (x2 + x2 + ↑x16) Bool.false = Bool.true }) →
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (2 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →             (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) →               have x12 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => if x12.op.eval [] = Bool.true ∧ x12.inputs.length = (2 : ℕ) ∧ (x12.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x12) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };               have x13 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x13 x14 : Fin x2) (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x13 ∨ x15 = Fin.natAdd x2 x14);               ∀ (x14 : Fin x2 → Finset (Fin x2)), (∀ (x15 x16 : Fin x2), x16 ∈ x14 x15 → x3 x16 x15 ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (x13 x16 x15) = Bool.true ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x12 (x13 x16 x15) = Bool.false) → ∑ x16 : Fin x2, (x14 x16).card ≤ (44 : ℕ) * Fintype.card { x16 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x16) Bool.false = Bool.false ∧ ∃ (x17 : Fin x2), ∃ x18 ∈ x14 x17, (x5.wires (List.ofFn (x13 x18 x17))).getD (x2 + x2 + ↑x16) Bool.false = Bool.true } := by
  intro hstruct hcut
  intro x1 x2 x3 x4 x5 hq hN hcol huniq hmin hsound
  intro D edge x14 hT
  have h0 : circuitFun (x2 + x2) x5 (fun _ => false) = false := by
    apply hsound
    · haveI : IsEmpty { x12 : Fin x2 // (fun _ : Fin (x2 + x2) => false) (Fin.natAdd x2 x12) = true } :=
        ⟨fun x => by simpa using x.2⟩
      simp
    · simp
  have hrep : List.ofFn (fun _ : Fin (x2 + x2) => false) = List.replicate (x2 + x2) false :=
    List.ofFn_const _ _
  have hout : (x5.wires (List.replicate (x2 + x2) false)).getD x5.output false = false := by
    change (x5.wires (List.ofFn (fun _ : Fin (x2 + x2) => false))).getD x5.output false = false at h0
    rwa [hrep] at h0
  have hno : ∀ x11 : Fin x5.size,
      (x5.wires (List.replicate (x2 + x2) false)).getD (x2 + x2 + ↑x11) false = false :=
    hstruct (x2 + x2) x5 hmin hout
  by_cases hk : ∃ x11 : Gate, x11 ∈ x5.gates ∧ (x11.op.eval [] = Bool.true ∧ x11.inputs.length = (2 : ℕ) ∧ (x11.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true)
  · exact hcut x1 x2 x3 x5 hq hN hcol huniq hmin hsound hno hk x14 hT
  · have hcond : ∀ g ∈ x5.gates, ¬ (g.op.eval [] = Bool.true ∧ g.inputs.length = (2 : ℕ) ∧ (g.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true) := by
      intro g hg hc
      exact hk ⟨g, hg, hc⟩
    have hmap : ∀ (gs : List Gate), (∀ g ∈ gs, ¬ (g.op.eval [] = Bool.true ∧ g.inputs.length = (2 : ℕ) ∧ (g.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true)) → gs.map (fun g : Gate => if (g.op.eval [] = Bool.true ∧ g.inputs.length = (2 : ℕ) ∧ (g.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true) then (⟨GateOp.or, []⟩ : Gate) else g) = gs := by
      intro gs
      induction gs with
      | nil => intro _; rfl
      | cons g tl ih =>
          intro hh
          have h1 : ¬ (g.op.eval [] = Bool.true ∧ g.inputs.length = (2 : ℕ) ∧ (g.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true) := hh g (by simp)
          have h2 : ∀ g' ∈ tl, ¬ (g'.op.eval [] = Bool.true ∧ g'.inputs.length = (2 : ℕ) ∧ (g'.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true) := fun g' hg' => hh g' (by simp [hg'])
          simp only [List.map_cons, if_neg h1]
          rw [ih h2]
    have hD : D = x5 := by
      have hmapx : List.map (fun g : Gate => if (g.op.eval [] = Bool.true ∧ g.inputs.length = (2 : ℕ) ∧ (g.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true) then (⟨GateOp.or, []⟩ : Gate) else g) x5.gates = x5.gates := hmap x5.gates hcond
      calc D = ({ gates := List.map (fun g : Gate => if (g.op.eval [] = Bool.true ∧ g.inputs.length = (2 : ℕ) ∧ (g.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true) then (⟨GateOp.or, []⟩ : Gate) else g) x5.gates, output := x5.output } : Circuit) := rfl
        _ = ({ gates := x5.gates, output := x5.output } : Circuit) := by rw [hmapx]
        _ = x5 := rfl
    have hzero : ∀ l : Fin x2, x14 l = ∅ := by
      intro l
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨p, hp⟩
      obtain ⟨-, htrue, hfalse⟩ := hT l p hp
      rw [hD] at hfalse
      rw [htrue] at hfalse
      simp at hfalse
    have hsum : ∑ x16 : Fin x2, (x14 x16).card = 0 := by
      simp [hzero]
    rw [hsum]
    exact Nat.zero_le _
