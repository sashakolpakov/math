import OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicEtaleMap

/-! # Active Boundary Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ActiveBoundaryNeighborhood.Construction

noncomputable section

/-! Actual open neighborhoods retaining exactly the boundary components through a chosen point. -/

variable {R σ : Type*} [CommRing R] [DecidableEq σ]

/-- Invert the product of boundary equations absent from the chosen point.
The logarithmic bound then holds for precisely the remaining boundary
components on that actual affine open. -/
theorem exists_active_boundary_neighborhood (w : σ → R) (B : Finset σ)
    (J q : Ideal R) [q.IsPrime] (n : ℕ)
    (hbound : LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal (fun i : B => w i.val) J n = ⊤) :
    ∃ (C : Finset σ) (f : R), C ⊆ B ∧ f ∉ q ∧
      (∀ i ∈ B, i ∈ C ↔ w i ∈ q) ∧
      (∀ i ∈ B, i ∉ C → IsUnit (algebraMap R (Localization.Away f) (w i))) ∧
      LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal
        (fun i : C => algebraMap R (Localization.Away f) (w i.val))
        (J.map (algebraMap R (Localization.Away f))) n = ⊤ := by
  classical
  let C := B.filter (fun i => w i ∈ q)
  let f := ∏ i ∈ B \ C, w i
  have hCB : C ⊆ B := Finset.filter_subset _ _
  have hf : f ∉ q := by
    apply q.primeCompl.prod_mem
    intro i hi
    obtain ⟨hiB, hiC⟩ := Finset.mem_sdiff.mp hi
    intro hwi
    exact hiC (Finset.mem_filter.mpr ⟨hiB, hwi⟩)
  have hunit : ∀ i ∈ B, i ∉ C → IsUnit (algebraMap R (Localization.Away f) (w i)) := by
    intro i hiB hiC
    apply IsLocalization.Away.isUnit_of_dvd (S := Localization.Away f) f
    exact Finset.dvd_prod_of_mem w (Finset.mem_sdiff.mpr ⟨hiB, hiC⟩)
  refine ⟨C, f, hCB, hf, ?_, hunit, ?_⟩
  · intro i hi
    simp only [C, Finset.mem_filter, hi, true_and]
  · let : Algebra.FormallyEtale R (Localization.Away f) :=
      Algebra.FormallyEtale.of_isLocalization (Submonoid.powers f)
    have hmap := LogarithmicEtaleMap.Construction.logarithmic_order_bound_map (S := Localization.Away f) (fun i : B => w i.val) J n hbound
    have hderiv := LogarithmicEtaleMap.Construction.logarithmicDerivations_remove_unit_components
      (fun i => algebraMap R (Localization.Away f) (w i)) B C hCB hunit
    rw [LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal_congr_derivations _ _ hderiv] at hmap
    exact hmap

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ActiveBoundaryNeighborhood.Construction
