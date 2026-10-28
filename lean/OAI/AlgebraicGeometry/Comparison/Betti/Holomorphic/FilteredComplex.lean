import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredSheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.MonoLift
import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD

/-! # Filtered Complex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredComplex.Hodge

noncomputable section

/-! The original holomorphic de Rham comparison factors from its actual
degree truncation through the genuine filtered smooth sheaf complex. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

def holomorphicFilteredTerm (r : ℤ) (n : ℕ) :
    Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term (C := SheafComplex.sheafCategory M) (SheafComplex.sheafComplex E M) r n ⟶
      (Filtered.SmoothComplex.Hodge.filteredFormSheaf E M n r : SheafComplex.sheafCategory M) :=
  if h : r ≤ (n : ℤ) then
    eqToHom (by simp only [Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, ite_eq_left h]) ≫ FilteredSheaf.Hodge.holomorphicToFilteredSheaf E M n r h
  else ObjectProperty.homMk 0

theorem holomorphicFilteredTerm_factorization (r : ℤ) (n : ℕ) :
    holomorphicFilteredTerm E M r n ≫ Filtered.SmoothComplex.Hodge.filteredFormSheafInclusion E M n r =
      Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm (SheafComplex.sheafComplex E M) r n ≫
        (SheafComplex.inclusionSheafMap E M).f n := by
  by_cases h : r ≤ (n : ℤ)
  · simp only [holomorphicFilteredTerm, Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_left h]
    erw [Category.assoc, FilteredSheaf.Hodge.holomorphicToFilteredSheaf_inclusion]
    rfl
  · simp only [holomorphicFilteredTerm, Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_right h]
    apply Sheaf.hom_ext
    exact Limits.zero_comp.trans Limits.zero_comp.symm

def holomorphicFilteredSheafMap (r : ℤ) :
    Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (SheafComplex.sheafComplex E M) r ⟶ Filtered.SmoothComplex.Hodge.filteredSmoothSheafComplex E M r := by
  have hmono (n : ℕ) : Mono ((Filtered.SmoothComplex.Hodge.filteredSmoothSheafInclusion E M r).f n) :=
    FilteredSheaf.Hodge.filteredFormSheafInclusion_mono E M n r
  exact Complex.MonoLift.liftAlongMono
    (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (SheafComplex.sheafComplex E M) r ≫ SheafComplex.inclusionSheafMap E M)
    (Filtered.SmoothComplex.Hodge.filteredSmoothSheafInclusion E M r) hmono (holomorphicFilteredTerm E M r)
    (holomorphicFilteredTerm_factorization E M r)

theorem holomorphicFilteredSheafMap_factorization (r : ℤ) :
    holomorphicFilteredSheafMap E M r ≫ Filtered.SmoothComplex.Hodge.filteredSmoothSheafInclusion E M r =
      Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (SheafComplex.sheafComplex E M) r ≫ SheafComplex.inclusionSheafMap E M := by
  have hmono (n : ℕ) : Mono ((Filtered.SmoothComplex.Hodge.filteredSmoothSheafInclusion E M r).f n) :=
    FilteredSheaf.Hodge.filteredFormSheafInclusion_mono E M n r
  exact Complex.MonoLift.liftAlongMono_factorization
    (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (SheafComplex.sheafComplex E M) r ≫ SheafComplex.inclusionSheafMap E M)
    (Filtered.SmoothComplex.Hodge.filteredSmoothSheafInclusion E M r) hmono (holomorphicFilteredTerm E M r)
    (holomorphicFilteredTerm_factorization E M r)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredComplex.Hodge
