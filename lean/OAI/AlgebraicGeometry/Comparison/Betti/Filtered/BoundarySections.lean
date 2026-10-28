import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredTermSections
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredComplex
import OAI.AlgebraicGeometry.Comparison.Betti.Brutal
import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.LocalPoincare

/-! # Boundary Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Filtered.BoundarySections.Hodge

noncomputable section

/-! Every closed filtered section at the truncation boundary has an
actual holomorphic preimage under the original comparison component. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem holomorphicFilteredSheafMap_f (r : ℤ) (n : ℕ) :
    (Holomorphic.FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r).f n = Holomorphic.FilteredComplex.Hodge.holomorphicFilteredTerm E M r n := rfl

theorem holomorphicFilteredTerm_eq (r : ℤ) (n : ℕ) (hr : r ≤ (n : ℤ)) :
    Holomorphic.FilteredComplex.Hodge.holomorphicFilteredTerm E M r n =
      Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm (Holomorphic.SheafComplex.sheafComplex E M) r n ≫ Holomorphic.FilteredSheaf.Hodge.holomorphicToFilteredSheaf E M n r hr := by
  simp only [Holomorphic.FilteredComplex.Hodge.holomorphicFilteredTerm, Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_left hr]

theorem holomorphicFilteredSheafMap_f_mono (r : ℤ) (n : ℕ) (hr : r ≤ (n : ℤ)) :
    Mono ((Holomorphic.FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r).f n) := by
  have hi := Brutal.Complex.brutal_inclusionTerm_isIso (Holomorphic.SheafComplex.sheafComplex E M) r n hr
  have hm := Holomorphic.FilteredTermSections.Hodge.holomorphicToFilteredSheaf_mono E M n r hr
  rw [holomorphicFilteredSheafMap_f, holomorphicFilteredTerm_eq E M r n hr]
  exact @CategoryTheory.mono_comp (Holomorphic.SheafComplex.sheafCategory M) _ _ _ _
    (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm (Holomorphic.SheafComplex.sheafComplex E M) r n) inferInstance
    (Holomorphic.FilteredSheaf.Hodge.holomorphicToFilteredSheaf E M n r hr) hm

theorem filtered_boundary_section_lift (U : Opens M) (r : ℤ) (n : ℕ) (hr : r ≤ (n : ℤ))
    (hboundary : n = 0 ∨ r = (n : ℤ))
    (y : Open.FiltrationDescent.Hodge.openFormFiltration (E := E) U n r) (hy : SmoothComplex.Hodge.filteredOpenDifferential E M U n r y = 0) :
    ∃ z : ((Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (Holomorphic.SheafComplex.sheafComplex E M) r).X n).obj.obj (op U),
      ((Holomorphic.FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r).f n).hom.app (op U) z = y := by
  have hytop : y.val ∈ Open.FiltrationDescent.Hodge.openFormFiltration U n (n : ℤ) := by
    rcases hboundary with hn | hrn
    · subst n
      change y.val ∈ Open.FiltrationDescent.Hodge.openFormFiltration U 0 0
      rw [LocalPoincare.Hodge.openFormFiltration_eq_top U 0 0 le_rfl]
      exact Submodule.mem_top
    · simpa only [hrn] using y.property
  have hyd : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d y.val = 0 := congrArg Subtype.val hy
  obtain ⟨A, hA, _⟩ := TopFilteredForms.Hodge.closed_topFiltered_holomorphic U n y.val hytop hyd
  let j := Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm (Holomorphic.SheafComplex.sheafComplex E M) r n
  have hj : IsIso j := Brutal.Complex.brutal_inclusionTerm_isIso (Holomorphic.SheafComplex.sheafComplex E M) r n hr
  let e := ((sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapIso (asIso j)).app (op U)
  refine ⟨e.inv ((Holomorphic.SheafSections.holomorphicSheafSectionIso E M U n).hom A), ?_⟩
  rw [holomorphicFilteredSheafMap_f, holomorphicFilteredTerm_eq E M r n hr]
  change (Holomorphic.FilteredSheaf.Hodge.holomorphicToFilteredSheaf E M n r hr).hom.app (op U)
    (e.hom (e.inv ((Holomorphic.SheafSections.holomorphicSheafSectionIso E M U n).hom A))) = y
  rw [Iso.inv_hom_id_apply, Holomorphic.FilteredTermSections.Hodge.holomorphicToFilteredSheaf_section]
  exact Subtype.ext hA

end

end OAI.AlgebraicGeometry.Comparison.Betti.Filtered.BoundarySections.Hodge
