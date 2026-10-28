import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module

/-! # Prime Divisor Immersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorImmersion.Constructions

noncomputable section

/-! The actual regular locus of a prime divisor instantiates the analytic
closed-immersion interface, with the same native charts and the same Thom class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] (z : {x : X.left // Order.coheight x = 1})

/-- The genuine open submanifold obtained by removing this divisor's singular boundary. -/
def regularAmbientManifold : Closed.ComplexImmersion.Constructions.ComplexManifold where
  complexDimension := Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom
  analyticSpace := TopCat.of (Scheme.RegularSupport.Constructions.regularAmbientOpen X (SchemeDivisor.Purity.Constructions.primeSupport X z))
  chartedSpace := inferInstance
  manifold := inferInstance
  metrizable := MetrizableSpace.subtype _

/-- The original reduced divisor's actual smooth locus and its actual closed inclusion. -/
def primeDivisorImmersion : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (regularAmbientManifold X z) 1 where
  regularComplexDimension := Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Scheme.RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)).hom
  regularAnalyticSpace := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Scheme.RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)))
  chartedSpace := inferInstance
  manifold := inferInstance
  regularComplementTopCatMap := TopCat.ofHom
    ⟨Scheme.RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z),
      (Scheme.RegularSupport.Constructions.regularComplementInclusion_closed X (SchemeDivisor.Purity.Constructions.primeSupport X z)).continuous⟩
  holomorphic := Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X (SchemeDivisor.Purity.Constructions.primeSupport X z) ω
  differential_injective := Scheme.RegularSupport.Constructions.regularComplementInclusion_mfderiv_injective X (SchemeDivisor.Purity.Constructions.primeSupport X z)
  closed := Scheme.RegularSupport.Constructions.regularComplementInclusion_closed X (SchemeDivisor.Purity.Constructions.primeSupport X z)
  regularComplexDimension_add_codimension := SchemeDivisor.Purity.Constructions.primeRegularDimension_add_one X z

/-- This interface retains the already constructed, normalized regular divisor class. -/
theorem primeDivisorImmersion_ThomClass :
    (primeDivisorImmersion X z).regularThomClass = SchemeDivisor.Module.Constructions.regularDivisorThomClass X z := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorImmersion.Constructions
