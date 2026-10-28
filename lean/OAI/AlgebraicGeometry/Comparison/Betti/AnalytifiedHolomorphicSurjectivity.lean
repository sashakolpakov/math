import OAI.AlgebraicGeometry.Comparison.Betti.SchemeHolomorphicBasisNeighborhoods
import OAI.AlgebraicGeometry.Comparison.Betti.AnalytifiedForm
import OAI.AlgebraicGeometry.Comparison.Betti.BasisRangeSurjectivity

/-! # Analytified Holomorphic Surjectivity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AnalytifiedHolomorphicSurjectivity

noncomputable section

/-! The actual analytified differential-module map is surjective on arbitrarily small neighborhoods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem analytifiedExteriorToHolomorphicModuleMap_localSurjective
    (O : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (p : O) (n : ℕ) :
    ∃ (W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)), W ≤ O ∧ (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) ∈ W ∧
      Function.Surjective ((AnalytifiedForm.analytifiedExteriorToHolomorphicModuleMap X n).val.app (op W)) := by
  obtain ⟨U, _, W, hW, hWO, hpW, I, _, b, hb⟩ :=
    SchemeHolomorphicBasisNeighborhoods.schemePoint_algebraicImages_localBasis_within X O p n
  refine ⟨W, hWO, hpW, ?_⟩
  apply BasisRangeSurjectivity.LinearAlgebra.surjective_of_basis_range
    (f := ((AnalytifiedForm.analytifiedExteriorToHolomorphicModuleMap X n).val.app (op W)).hom) b
  intro i
  obtain ⟨a, ha⟩ := hb i
  exact ⟨AnalytifiedForm.analytifiedFormSectionOn X U W hW n a,
    (AnalytifiedForm.analytifiedFormSectionOn_comparison X U W hW n a).trans ha.symm⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.AnalytifiedHolomorphicSurjectivity
