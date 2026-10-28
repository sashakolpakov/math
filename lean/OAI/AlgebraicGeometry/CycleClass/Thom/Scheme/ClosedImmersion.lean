import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothImmersion

/-! # Closed Immersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions

noncomputable section

/-! Actual closed immersions of smooth integral complex schemes give
the native closed complex immersions used by supported Thom pushforward. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothImmersion
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions

abbrev schemeManifold (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] : Closed.ComplexImmersion.Constructions.ComplexManifold where
  complexDimension := Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom
  analyticSpace := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  chartedSpace := inferInstance
  manifold := inferInstance
  metrizable := inferInstance

abbrev schemeClosedImmersion {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] (i : X ⟶ Y) [IsClosedImmersion i.left]
    (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) :
    Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (schemeManifold Y) p where
  regularComplexDimension := Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom
  regularAnalyticSpace := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  chartedSpace := inferInstance
  manifold := inferInstance
  regularComplementTopCatMap := TopCat.ofHom
    ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map i⟩
  holomorphic := ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map i ω
  differential_injective := ComplexPoints.Analytic.IntrinsicSmoothImmersion.mfderiv_nativeScheme_immersion_injective i
  closed := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion i
  regularComplexDimension_add_codimension := hp

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions
