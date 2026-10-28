import OAI.AlgebraicGeometry.Comparison.Betti.Affine.SchemeStalkNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RingedStalkCharts

/-! # Scheme Stalk Centers -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.SchemeStalkCenters

noncomputable section

/-! Affine chart stalk identifications at an explicitly identified native scheme point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RingedStalkCharts.AnalyticLocal

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  (U : X.left.Opens) (hU : IsAffineOpen U)
  (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (RegularSmoothness.NativeModel X))
  (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
    (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom))
  (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (hx : x ∈ e.source)
  (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hp : p = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU x)

def affineSchemeChartStalkEquivAt : ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X p ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x) := by
  subst p
  exact SchemeStalkNormalization.affineSchemeChartStalkEquiv X U hU e he x hx

theorem affineSchemeChartStalkEquivAt_algebraic_germ
    (hpU : Analytification.Base.analytificationMap X p ∈ U) (s : Γ(X.left, U)) :
    affineSchemeChartStalkEquivAt X U hU e he x hx p hp
      (ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap X p (X.left.presheaf.germ U (Analytification.Base.analytificationMap X p) hpU s)) =
        ChartGermMap.AnalyticLocal.affineChartGermMap e he x hx s := by
  subst p
  exact SchemeStalkNormalization.affineSchemeChartStalkEquiv_algebraic_germ X U hU e he x hx hpU s

theorem affineSchemeChartStalkEquivAt_eq_chart :
    affineSchemeChartStalkEquivAt X U hU e he x hx p hp =
      Holomorphic.RingedStalkCharts.AnalyticLocal.chartStructureStalkEquivAt (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
        (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
          (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) e)
        (show ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
          (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) e ∈
          atlas (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) from ⟨U, hU, e, he, rfl⟩) p
        (by rw [hp]; exact ⟨x, hx, rfl⟩) (e x)
        (by
          rw [hp]
          exact ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
            (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) e x) := by
  subst p
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.SchemeStalkCenters
