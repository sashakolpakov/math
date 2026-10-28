import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedCycleClass
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition

/-! # Support Regular Immersion -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportRegularImmersion.BundleCycles

noncomputable section

/-! The actual regular locus of an arbitrary integral support is a
closed complex immersion in the complement of its singular boundary. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold
open scoped _root_.Manifold ContDiff

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] (Z : IrreducibleCloseds X.left) (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

abbrev schemeSupportRegularImmersion :
    CycleClass.Thom.Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeManifold X) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z)) p where
  regularComplexDimension := Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z).hom
  regularAnalyticSpace := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z))
  chartedSpace := inferInstance
  manifold := inferInstance
  regularComplementTopCatMap := TopCat.ofHom
    ⟨CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z, (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X Z)).subtype_mk _⟩
  holomorphic := CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω
  differential_injective := CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_mfderiv_injective X Z
  closed := CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_closed X Z
  regularComplexDimension_add_codimension :=
    (congrArg (fun n => n + p) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularDimension_eq X Z)).trans
      (hp.trans (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension X.hom))

theorem schemeSupportRegularImmersion_Thom [AlgebraicGeometry.IsNoetherian X.left] :
    (schemeSupportRegularImmersion X Z p hp).regularThomClass = SupportedCycleClass.BundleCycles.schemeRegularSupportThomClass X Z p hp := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportRegularImmersion.BundleCycles
