import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open scoped BigOperators

theorem PEqualNP.Outside.R_meta_2076_512
    (support : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → G.support.ncard ≤ C.size + 1)
    (peel : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (S : Finset (Fin n)) (w : Fin n → ℕ),
      H.support ⊆ (S : Set (Fin n)) →
      ∃ K : SimpleGraph (Fin n), K ≤ H ∧
        (∀ v : Fin n, (K.neighborSet v).ncard = 0 ∨ w v < (K.neighborSet v).ncard) ∧
        H.edgeSet.ncard ≤ K.edgeSet.ncard + ∑ v ∈ S, w v)
    (priced : ∃ (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (5 : ℕ) ≤ p.length) →
      ∀ (C : Circuit), IsLeastAO G C → TopForm G C →
      ∀ S ⊆ Ustar G C,
      (∀ (e : Sym2 (Fin n)), e ∈ S →
        ∃ (u v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C, ∀ (b : Fin 2),
          u ∈ side (n := n) C a b ∨ v ∈ side (n := n) C a b ∨
          ∃ g ∈ junk G C, PEqualNP.CleanedNonEdge.OrReaches n C (opnd C a b) g ∧
            ((∀ (b' : Fin 2), u ∈ side (n := n) C g b' ∨ v ∈ side (n := n) C g b') ∨
              ∃ (b' : Fin 2), u ∈ side (n := n) C a (1 - b) ∧
                (u ∈ side (n := n) C g b' ∨ v ∈ side (n := n) C g b') ∧
                ∃ g' ∈ junk G C, PEqualNP.CleanedNonEdge.OrReaches n C (opnd C g (1 - b')) g' ∧
                  ∀ (b'' : Fin 2), u ∈ side (n := n) C g' b'' ∨ v ∈ side (n := n) C g' b'')) →
      S.card ≤ c * (C.size + 1))
    (residual : ∃ (k : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (5 : ℕ) ≤ p.length) →
      G.edgeFinset.Nonempty →
      ∀ (C : Circuit) (H : SimpleGraph (Fin n)),
      IsLeastAO G C → TopForm G C →
      H ≤ G.deleteEdges (starEdges G C : Set (Sym2 (Fin n))) →
      (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨
        2 + 4 * (C.gates.flatMap Gate.inputs).count v.val < (H.neighborSet v).ncard) →
      ∀ (S : Finset (Sym2 (Fin n))),
      (∀ (e : Sym2 (Fin n)), e ∈ S → e ∈ H.edgeSet ∧
        ¬ (∃ (u v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C, ∀ (b : Fin 2),
          u ∈ side (n := n) C a b ∨ v ∈ side (n := n) C a b ∨
          ∃ g ∈ junk G C, PEqualNP.CleanedNonEdge.OrReaches n C (opnd C a b) g ∧
            ((∀ (b' : Fin 2), u ∈ side (n := n) C g b' ∨ v ∈ side (n := n) C g b') ∨
              ∃ (b' : Fin 2), u ∈ side (n := n) C a (1 - b) ∧
                (u ∈ side (n := n) C g b' ∨ v ∈ side (n := n) C g b') ∧
                ∃ g' ∈ junk G C, PEqualNP.CleanedNonEdge.OrReaches n C (opnd C g (1 - b')) g' ∧
                  ∀ (b'' : Fin 2), u ∈ side (n := n) C g' b'' ∨ v ∈ side (n := n) C g' b''))) →
      S.card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : SimpleGraph (Fin x2)), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → x8 ≤ x3.deleteEdges ↑(PEqualNP.TopForm.starEdges x3 x7) → (∀ (x12 : Fin x2), (x8.neighborSet x12).ncard = (0 : ℕ) ∨ (3 : ℕ) ≤ (x8.neighborSet x12).ncard) → x8.edgeSet.ncard ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨c, hPriced⟩ := priced
  obtain ⟨k, hResid⟩ := residual
  refine ⟨c + k + 10, ?_⟩
  intro n G _ hGirth hEdge C H hLeast hTop hInside hDeg
  have edgeCount (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
      F.edgeSet.ncard = F.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  let S0 := (Set.toFinite G.support).toFinset
  have sBound : S0.card ≤ C.size + 1 := by
    rw [← Set.ncard_eq_toFinset_card G.support (Set.toFinite G.support)]
    exact support n G C hLeast
  have hSub : H.support ⊆ (S0 : Set (Fin n)) := by
    rintro v ⟨u, hu⟩
    have hv : v ∈ G.support := ⟨u, (G.deleteEdges_le _) (hInside hu)⟩
    simpa only [S0, Finset.mem_coe, Set.Finite.mem_toFinset] using hv
  let pins := C.gates.flatMap Gate.inputs
  have sumPins : (∑ v ∈ S0, pins.count v.val) ≤ pins.length := by
    let T := S0.image Fin.val
    have reindex : (∑ i ∈ T, pins.count i) = ∑ v ∈ S0, pins.count v.val := by
      unfold T
      exact Finset.sum_image (fun _ _ _ _ eq => Fin.ext eq)
    let P := pins.toFinset
    have onlyUsed : (∑ i ∈ T ∩ P, pins.count i) = ∑ i ∈ T, pins.count i := by
      apply Finset.sum_subset Finset.inter_subset_left
      intro i ti skipped
      apply List.count_eq_zero_of_not_mem
      intro ip
      exact skipped (Finset.mem_inter.mpr ⟨ti, List.mem_toFinset.mpr ip⟩)
    rw [← reindex, ← onlyUsed]
    exact (Finset.sum_le_sum_of_subset Finset.inter_subset_right).trans
      (List.sum_toFinset_count_eq_length pins).le
  have slots (gs : List Gate) (fanin : ∀ g ∈ gs, g.inputs.length ≤ 2) :
      (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      have hv := fanin g (by simp)
      have tail := ih (fun h hh => fanin h (List.mem_cons_of_mem _ hh))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  have slotBudget : pins.length ≤ 2 * C.size :=
    slots C.gates (fun g hg => (hLeast.1.2.2 g hg).le)
  let w (v : Fin n) := 2 + 4 * pins.count v.val
  have weights : (∑ v ∈ S0, w v) ≤ 10 * (C.size + 1) := by
    have const : (∑ _ ∈ S0, (2 : ℕ)) = S0.card * 2 := Finset.sum_const_nat (by simp)
    have mult : (∑ v ∈ S0, 4 * pins.count v.val) = 4 * ∑ v ∈ S0, pins.count v.val := by
      rw [Finset.mul_sum]
    simp only [w, Finset.sum_add_distrib, const, mult]
    omega
  obtain ⟨K, hKH, hHeavy, hPaid⟩ := peel n H S0 w hSub
  have hKInside : K ≤ G.deleteEdges (starEdges G C : Set (Sym2 (Fin n))) := hKH.trans hInside
  have heavy' : ∀ v : Fin n, (K.neighborSet v).ncard = 0 ∨
      2 + 4 * (C.gates.flatMap Gate.inputs).count v.val < (K.neighborSet v).ncard := by
    intro v
    have hv := hHeavy v
    simpa only [w] using hv
  let pr : Sym2 (Fin n) → Prop := fun e =>
    ∃ (u v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C, ∀ (b : Fin 2),
      u ∈ side (n := n) C a b ∨ v ∈ side (n := n) C a b ∨
      ∃ g ∈ junk G C, PEqualNP.CleanedNonEdge.OrReaches n C (opnd C a b) g ∧
        ((∀ (b' : Fin 2), u ∈ side (n := n) C g b' ∨ v ∈ side (n := n) C g b') ∨
          ∃ (b' : Fin 2), u ∈ side (n := n) C a (1 - b) ∧
            (u ∈ side (n := n) C g b' ∨ v ∈ side (n := n) C g b') ∧
            ∃ g' ∈ junk G C, PEqualNP.CleanedNonEdge.OrReaches n C (opnd C g (1 - b')) g' ∧
              ∀ (b'' : Fin 2), u ∈ side (n := n) C g' b'' ∨ v ∈ side (n := n) C g' b'')
  let bad := K.edgeFinset.filter fun e : Sym2 (Fin n) => ¬ pr e
  let good := K.edgeFinset \ bad
  have hsplit : good.card + bad.card = K.edgeFinset.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (s := K.edgeFinset) _)
  have goodUstar : good ⊆ Ustar G C := by
    intro e he
    have heK : e ∈ K.edgeFinset := (Finset.mem_sdiff.mp he).1
    have hmem := SimpleGraph.edgeFinset_mono hKInside heK
    rw [SimpleGraph.edgeFinset_deleteEdges] at hmem
    simpa only [Ustar] using hmem
  have goodCond : ∀ (e : Sym2 (Fin n)), e ∈ good → pr e := by
    intro e he
    have heK : e ∈ K.edgeFinset := (Finset.mem_sdiff.mp he).1
    have hne : e ∉ bad := (Finset.mem_sdiff.mp he).2
    by_contra h
    exact hne (Finset.mem_filter.mpr ⟨heK, h⟩)
  have hGood := hPriced n G hGirth C hLeast hTop good goodUstar goodCond
  have badCond : ∀ (e : Sym2 (Fin n)), e ∈ bad → e ∈ K.edgeSet ∧ ¬ pr e := by
    intro e he
    have heK : e ∈ K.edgeFinset := (Finset.mem_filter.mp he).1
    refine ⟨?_, (Finset.mem_filter.mp he).2⟩
    simpa only [← SimpleGraph.coe_edgeFinset, Finset.mem_coe] using heK
  have hBad := hResid n G hGirth hEdge C K hLeast hTop hKInside heavy' bad badCond
  have hKcount : K.edgeSet.ncard = good.card + bad.card := by
    rw [edgeCount K, ← hsplit]
  rw [hKcount] at hPaid
  have hTarget : (c + k + 10) * (C.size + 1) =
      c * (C.size + 1) + k * (C.size + 1) + 10 * (C.size + 1) := by ring
  rw [hTarget]
  omega
