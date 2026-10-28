import OAI.AlgebraicGeometry.Comparison.Betti.PolydiscCoefficientElimination
import OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.ContractionVanishing

/-! # Higher Polydisc Iteration -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.HigherPolydiscIteration.Dolbeault

noncomputable section

/-! Finite iteration of the actual Cauchy corrections gives local
Dolbeault primitives of the correct pure type in every degree at least two. -/

open _root_.TopologicalSpace

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem coordinatePolydisc_mono (U V : ι → Opens ℂ) (h : ∀ i, V i ≤ U i) :
    DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc V ≤ DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc U := by
  intro x hx
  exact (DivisorClass.Chern.Complex.CoordinateSplit.mem_coordinatePolydisc U x).mpr (fun i => h i ((DivisorClass.Chern.Complex.CoordinateSplit.mem_coordinatePolydisc V x).mp hx i))

omit [Fintype ι] in
theorem coordinateOpen_update_le (V : ι → Opens ℂ) (i : ι) (W : Opens ℂ) (hW : W ≤ V i) :
    ∀ j, Function.update V i W j ≤ V j := by
  intro j
  by_cases h : j = i
  · subst j
    simpa only [Function.update_self] using hW
  · rw [Function.update_of_ne h]

theorem exists_polydisc_higherForm_eliminate_finset (U : ι → Opens ℂ)
    (n p q : ℕ) (hn : n + 1 = p + q)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc U) (n + 2)) (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) a = 0)
    (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a) (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc U) (s : Finset ι) :
    ∃ V : ι → Opens ℂ, ∃ hVU : ∀ i, V i ≤ U i, x.val ∈ DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc V ∧
      ∃ b : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc V) (n + 2),
      ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc V) (n + 1),
        b + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) t = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (coordinatePolydisc_mono U V hVU) a ∧
          DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) b = 0 ∧ DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) b ∧
          DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q t ∧
          ∀ i ∈ s, Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ (n + 1) (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector i) b = 0 := by
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨U, fun i => le_refl (U i), x.property, a, 0, ?_, ha, hpure, ?_, ?_⟩
      · rw [(DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (U := DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc U) (n + 1)).map_zero, add_zero]
        exact (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_refl a).symm
      · intro y z v
        change (0 : ℂ) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * 0
        exact (mul_zero _).symm
      · intro i hi
        exact False.elim (Finset.notMem_empty i hi)
  | @insert i s hi ih =>
      obtain ⟨V, hVU, hxV, b, t, hsum, hb, hbp, htp, hzero⟩ := ih
      obtain ⟨W, hxW, hWV, c, u, hstep, hc, hcp, hup, hci, hcprior⟩ :=
        PolydiscCoefficientElimination.Dolbeault.exists_polydisc_higherForm_coefficient_elimination V n p q hn b hb hbp ⟨x, hxV⟩ i
      let V' := Function.update V i W
      let hnew := DivisorClass.Chern.CoordinatePolydiscUpdate.coordinatePolydisc_update_le V i W hWV
      have hV'U : ∀ j, V' j ≤ U j := fun j => (coordinateOpen_update_le V i W hWV j).trans (hVU j)
      let t' : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc V') (n + 1) := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hnew t + u
      have hsum' : c + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) t' =
          Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (coordinatePolydisc_mono U V' hV'U) a := by
        have hrestrict := congrArg (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (n := n + 2) hnew) hsum
        rw [(Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (n := n + 2) hnew).map_add,
          DivisorClass.Chern.DolbeaultZeroKernelMap.openDolbeaultD_restrict, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_trans] at hrestrict
        calc
          c + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) t' =
              (c + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) u) + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hnew t) := by
            change c + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hnew t + u) = _
            rw [map_add]
            abel
          _ = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hnew b + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hnew t) := by
            rw [hstep]
          _ = _ := hrestrict
      have ht'p : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q t' :=
        DivisorClass.Chern.Open.DolbeaultSquared.openFormHasBidegree_add (DivisorClass.Chern.Open.DolbeaultPrime.openFormHasBidegree_restrict hnew htp) hup
      refine ⟨V', hV'U, DivisorClass.Chern.CoordinatePolydiscUpdate.coordinatePolydisc_update_mem V i W x hxV hxW,
        c, t', hsum', hc, hcp, ht'p, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjs
      · subst j
        exact hci
      · exact hcprior j (fun hji => hi (hji ▸ hjs)) (hzero j hjs)

theorem exists_polydisc_higherForm_dolbeault_primitive (U : ι → Opens ℂ)
    (n p q : ℕ) (hn : n + 1 = p + q)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc U) (n + 2)) (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) a = 0)
    (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a) (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc U) :
    ∃ V : ι → Opens ℂ, ∃ hVU : ∀ i, V i ≤ U i, x.val ∈ DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc V ∧
      ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc V) (n + 1), DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q t ∧
        DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) t = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (coordinatePolydisc_mono U V hVU) a := by
  obtain ⟨V, hVU, hxV, b, t, hsum, _, hbp, htp, hzero⟩ :=
    exists_polydisc_higherForm_eliminate_finset U n p q hn a ha hpure x Finset.univ
  have hbzero := Coordinate.ContractionVanishing.Dolbeault.pureOpenForm_eq_zero_of_coordinate_contractions (n + 1) p q hn b hbp
    (fun i => hzero i (Finset.mem_univ i))
  refine ⟨V, hVU, hxV, t, htp, ?_⟩
  simpa only [hbzero, zero_add] using hsum

end

end OAI.AlgebraicGeometry.Comparison.Betti.HigherPolydiscIteration.Dolbeault
