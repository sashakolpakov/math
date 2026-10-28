import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.SmoothComplex
import OAI.AlgebraicGeometry.Comparison.Betti.MapCochainOf

/-! # Presheaf Complex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Filtered.PresheafComplex.Hodge

noncomputable section

/-! The actual filtered smooth presheaf complex and the exact underlying
presheaf identification of its sheaf complex. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

def filteredSmoothPresheafComplex (r : ℤ) :
    CochainComplex ((TopCat.of M).Presheaf (ModuleCat.{0} ℂ)) ℕ :=
  CochainComplex.of (fun n => SmoothComplex.Hodge.filteredFormPresheaf E M n r)
    (fun n => SmoothComplex.Hodge.filteredFormPresheafD E M n r) (fun n => SmoothComplex.Hodge.filteredFormPresheafD_squared E M n r)

theorem filteredSmoothPresheafComplex_d (r : ℤ) (n : ℕ) :
    (filteredSmoothPresheafComplex E M r).d n (n + 1) = SmoothComplex.Hodge.filteredFormPresheafD E M n r :=
  CochainComplex.of_d (fun k => SmoothComplex.Hodge.filteredFormPresheaf E M k r)
    (fun k => SmoothComplex.Hodge.filteredFormPresheafD E M k r) n

variable [FiniteDimensional ℝ E]

def filteredSmoothSheafUnderlyingIso (r : ℤ) :
    ((sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapHomologicalComplex
      (.up ℕ)).obj (SmoothComplex.Hodge.filteredSmoothSheafComplex E M r) ≅ filteredSmoothPresheafComplex E M r :=
  MapCochainOf.Complex.mapCochainOfIso
    (sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ))
    (fun n => SmoothComplex.Hodge.filteredFormSheaf E M n r) (fun n => SmoothComplex.Hodge.filteredFormSheafD E M n r)
    (fun n => SmoothComplex.Hodge.filteredFormSheafD_squared E M n r)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Filtered.PresheafComplex.Hodge
