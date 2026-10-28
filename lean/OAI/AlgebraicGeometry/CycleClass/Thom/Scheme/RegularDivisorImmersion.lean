import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition

/-! # Regular Divisor Immersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularDivisorImmersion.Constructions

noncomputable section

/-! The actual regular locus of any prime divisor is a closed complex
immersion in the complement of its singular boundary. Its bundled Thom
class is exactly the canonical regular divisor Thom class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
  SchemeDivisor.Module.Constructions Open.ClosedImmersionComposition.Constructions.ComplexManifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] (z : {x : X.left // Order.coheight x = 1})

abbrev regularPrimeImmersion :
    Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold (ClosedImmersion.Constructions.schemeManifold X) (RegularSupport.Constructions.regularAmbientOpen X (SchemeDivisor.Purity.Constructions.primeSupport X z))) 1 where
  regularComplexDimension := Betti.AffineDimension.Realization.functionFieldDifferentialDimension (RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)).hom
  regularAnalyticSpace := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)))
  chartedSpace := inferInstance
  manifold := inferInstance
  regularComplementTopCatMap := TopCat.ofHom
    ⟨RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z),
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (RegularSupport.Constructions.regularToAmbient X (SchemeDivisor.Purity.Constructions.primeSupport X z))).subtype_mk _⟩
  holomorphic := RegularSupport.Constructions.regularComplementInclusion_contMDiff X (SchemeDivisor.Purity.Constructions.primeSupport X z) ω
  differential_injective := RegularSupport.Constructions.regularComplementInclusion_mfderiv_injective X (SchemeDivisor.Purity.Constructions.primeSupport X z)
  closed := RegularSupport.Constructions.regularComplementInclusion_closed X (SchemeDivisor.Purity.Constructions.primeSupport X z)
  regularComplexDimension_add_codimension := SchemeDivisor.Purity.Constructions.primeRegularDimension_add_one X z

theorem regularPrimeImmersion_Thom :
    (regularPrimeImmersion X z).regularThomClass = SchemeDivisor.Module.Constructions.regularDivisorThomClass X z := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularDivisorImmersion.Constructions
