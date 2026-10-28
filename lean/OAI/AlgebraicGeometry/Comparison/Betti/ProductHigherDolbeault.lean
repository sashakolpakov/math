import OAI.AlgebraicGeometry.Comparison.Betti.ProductCoordinateHigherElimination
import OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.ContractionVanishing

/-! # Product Higher Dolbeault -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProductHigherDolbeault

noncomputable section

/-! Global Dolbeault primitives of the original pure type in every
degree at least two on products of ordinary and punctured complex lines. -/

open _root_.TopologicalSpace

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_product_higherForm_eliminate_finset (ε : ι → Bool) (n p q : ℕ) (hn : n + 1 = p + q)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) (n + 2)) (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) a = 0)
    (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a) (s : Finset ι) :
    ∃ b : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) (n + 2),
    ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) (n + 1),
      b + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) t = a ∧ DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) b = 0 ∧
        DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) b ∧ DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q t ∧
        ∀ i ∈ s, Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ (n + 1) (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector i) b = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨a, 0, ?_, ha, hpure, ?_, ?_⟩
    · rw [map_zero, add_zero]
    · intro y z v
      change (0 : ℂ) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * 0
      exact (mul_zero _).symm
    · intro i hi
      exact False.elim (Finset.notMem_empty i hi)
  | @insert i s hi ih =>
    obtain ⟨b, t, hsum, hb, hbp, htp, hzero⟩ := ih
    obtain ⟨c, u, hstep, hc, hcp, hup, hci, hcprior⟩ :=
      ProductCoordinateHigherElimination.Dolbeault.exists_product_coordinate_higherForm_elimination ε n p q hn b hb hbp i
    refine ⟨c, t + u, ?_, hc, hcp, DivisorClass.Chern.Open.DolbeaultSquared.openFormHasBidegree_add htp hup, ?_⟩
    · calc
        c + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) (t + u) =
            (c + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) u) + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) t := by
          rw [map_add]
          abel
        _ = b + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) t := by rw [hstep]
        _ = a := hsum
    · intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjs
      · subst j
        exact hci
      · exact hcprior j (fun hji => hi (hji ▸ hjs)) (hzero j hjs)

theorem exists_product_higherForm_dolbeault_primitive (ε : ι → Bool) (n p q : ℕ) (hn : n + 1 = p + q)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) (n + 2)) (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) a = 0)
    (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a) :
    ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) (n + 1),
      DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q t ∧ DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) t = a := by
  obtain ⟨b, t, hsum, _, hbp, htp, hzero⟩ :=
    exists_product_higherForm_eliminate_finset ε n p q hn a ha hpure Finset.univ
  have hbzero := Coordinate.ContractionVanishing.Dolbeault.pureOpenForm_eq_zero_of_coordinate_contractions (n + 1) p q hn b hbp
    (fun i => hzero i (Finset.mem_univ i))
  exact ⟨t, htp, by simpa only [hbzero, zero_add] using hsum⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProductHigherDolbeault
