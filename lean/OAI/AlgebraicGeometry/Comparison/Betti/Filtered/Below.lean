import OAI.AlgebraicGeometry.Comparison.Betti.Brutal
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredComplex

/-! # Below -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Filtered.Below.Hodge

noncomputable section

/-! Both sides of the actual filtered comparison vanish in every
degree below its integer truncation index. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem filteredFormPresheaf_isZero_below (n : ℕ) (r : ℤ) (hr : (n : ℤ) < r) :
    IsZero (SmoothComplex.Hodge.filteredFormPresheaf E M n r) := by
  apply Functor.isZero
  intro U
  apply ModuleCat.isZero_of_iff_subsingleton.mpr
  have hz (a : Open.FiltrationDescent.Hodge.openFormFiltration (E := E) U.unop n r) : a.val = 0 := by
    apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U.unop n).injective
    have ha : Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U.unop n a.val ∈ ManifoldFormFiltration.Hodge.manifoldFormFiltration E U.unop n r := a.property
    rw [ManifoldFormFiltration.Hodge.manifoldFormFiltration_eq_bot E U.unop n r hr] at ha
    have he : Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U.unop n a.val = 0 := ha
    simpa only [map_zero] using he
  exact ⟨fun a b => Subtype.ext ((hz a).trans (hz b).symm)⟩

variable [FiniteDimensional ℝ E]

theorem filteredFormSheaf_isZero_below (n : ℕ) (r : ℤ) (hr : (n : ℤ) < r) :
    IsZero (SmoothComplex.Hodge.filteredFormSheaf E M n r) :=
  IsZero.of_full_of_faithful_of_isZero
    (sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ))
    (SmoothComplex.Hodge.filteredFormSheaf E M n r) (filteredFormPresheaf_isZero_below E M n r hr)

theorem holomorphicFilteredSheafMap_quasiIsoAt_below (r : ℤ) (n : ℕ) (hr : (n : ℤ) < r) :
    QuasiIsoAt (Holomorphic.FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r) n := by
  have hsource := Brutal.Complex.brutal_isZero_X_below (Holomorphic.SheafComplex.sheafComplex E M) r n hr
  apply (quasiIsoAt_iff_exactAt _ n (ExactAt.of_isZero hsource)).mpr
  exact ExactAt.of_isZero (filteredFormSheaf_isZero_below E M n r hr)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Filtered.Below.Hodge
