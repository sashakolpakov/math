import OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkMap
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartGermMap
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenSectionEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.GermMaps

/-! # Scheme Stalk Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.SchemeStalkNormalization

noncomputable section

/-! In every native affine scheme chart, the original holomorphic
structure stalk and original regular section map agree with actual
affine algebra evaluation in the chart germ ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Filter
open scoped _root_.Topology _root_.Manifold ContDiff

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  (U : X.left.Opens) (hU : IsAffineOpen U)
  (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (RegularSmoothness.NativeModel X))
  (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
    (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom))
  (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (hx : x ∈ e.source)

local notation "chartC" => OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) e
local notation "p" => OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU x

def affineSchemeChartStalkEquiv : ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X p ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x) := by
  have hc : chartC ∈ atlas (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := ⟨U, hU, e, he, rfl⟩
  have hpc : p ∈ (chartC).source := ⟨x, hx, rfl⟩
  exact (ManifoldHolomorphicStalk.AnalyticLocal.chartStructureStalkEquiv (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) chartC hc p hpc).trans
      (Holomorphic.GermMaps.AnalyticLocal.holomorphicGermPointEquiv (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) e x))

theorem affineSchemeChartStalkEquiv_section (hp : Analytification.Base.analytificationMap X p ∈ U) (s : Γ(X.left, U)) :
    affineSchemeChartStalkEquiv X U hU e he x hx
      (TopCat.Presheaf.germ (C := RingCat) (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).obj (Open.AffineIsoEvaluation.analyticOpen X U) p hp
          (Holomorphic.RegularSections.regularHolomorphicSectionMap X U s)) = ChartGermMap.AnalyticLocal.affineChartGermMap e he x hx s := by
  have hc : chartC ∈ atlas (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := ⟨U, hU, e, he, rfl⟩
  have hpc : p ∈ (chartC).source := ⟨x, hx, rfl⟩
  have hnorm := ManifoldHolomorphicStalk.AnalyticLocal.chartStructureStalkEquiv_germ (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) chartC hc p hpc
    (Open.AffineIsoEvaluation.analyticOpen X U) hp (Holomorphic.RegularSections.regularHolomorphicSectionMap X U s)
  apply Subtype.ext
  apply Holomorphic.GermMaps.AnalyticLocal.holomorphicGermPointEquiv_val _ _ (fun z => e.symm z s)
  apply Eq.trans (congrArg Subtype.val hnorm)
  apply Germ.coe_eq.mpr
  filter_upwards [(Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen chartC (Open.AffineIsoEvaluation.analyticOpen X U)).isOpen.mem_nhds
    (Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen chartC (Open.AffineIsoEvaluation.analyticOpen X U) hpc hp)] with z hz
  change Holomorphic.CoefficientMem.openCoefficientExtension (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen chartC (Open.AffineIsoEvaluation.analyticOpen X U))
    (Holomorphic.ChartStalkGerms.AnalyticLocal.chartFunctionSection chartC hc (Open.AffineIsoEvaluation.analyticOpen X U) (Holomorphic.RegularSections.regularHolomorphicSectionMap X U s)).val z = e.symm z s
  rw [Holomorphic.CoefficientMem.openCoefficientExtension_apply (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen chartC (Open.AffineIsoEvaluation.analyticOpen X U)) _ ⟨z, hz⟩]
  change Open.AffineIsoEvaluation.sectionEvaluationOn X U s ⟨(chartC).symm z, hz.2⟩ = e.symm z s
  have hpz : (⟨(chartC).symm z, hz.2⟩ : Open.AffineIsoEvaluation.analyticOpen X U) = OpenSectionEvaluation.affineOpenPointInOpen X U hU (e.symm z) := by
    apply Subtype.ext
    exact (OpenSectionEvaluation.affineOpenPointInOpen_val X U hU (e.symm z)).symm
  rw [hpz]
  exact OpenSectionEvaluation.sectionEvaluationOn_affineOpen X U hU (e.symm z) s

theorem affineSchemeChartStalkEquiv_algebraic_germ (hp : Analytification.Base.analytificationMap X p ∈ U) (s : Γ(X.left, U)) :
    affineSchemeChartStalkEquiv X U hU e he x hx
      (ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap X p (X.left.presheaf.germ U (Analytification.Base.analytificationMap X p) hp s)) =
        ChartGermMap.AnalyticLocal.affineChartGermMap e he x hx s :=
  (congrArg (affineSchemeChartStalkEquiv X U hU e he x hx)
    (ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap_germ X p U hp s)).trans
      (affineSchemeChartStalkEquiv_section X U hU e he x hx hp s)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.SchemeStalkNormalization
