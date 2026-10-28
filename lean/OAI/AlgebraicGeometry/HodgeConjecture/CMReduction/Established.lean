import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.FourFactorSwitches
import OAI.Algebra.FieldTheory.ScalarDescentTrace
import OAI.AlgebraicGeometry.HodgeConjecture.PairSwitches
import OAI.AlgebraicGeometry.HodgeConjecture.CycleCoefficientsP
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Algebraicity
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.RationalHodge
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.RiemannRealization
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CycleClasses
import OAI.AlgebraicGeometry.AbelianVariety.ExteriorCohomology
import OAI.AlgebraicGeometry.Cycles.Functoriality.DimensionPreserving
import OAI.AlgebraicGeometry.Cycles.Functoriality.Resolution
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ChowNaturality
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.GraphPullback
import OAI.AlgebraicGeometry.CycleClass.Thom.Exterior
import OAI.Analysis.HodgeTheory.PolarizedPairing
import OAI.AlgebraicGeometry.Resolution.Blowups.Strong
import OAI.Analysis.HodgeTheory.Decomposition.Constructions
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Definitions

/-! # Established -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.CMReduction.Established

/-! All inputs of the original CMReduction reduction supplied by proved results. -/

theorem scalarTrace : Descent.CM.Construction.ScalarDescentInput :=
  Algebra.FieldTheory.ScalarDescentTrace.Core.scalar_trace_descent

theorem connectivity : Paths.CM.Construction.PairSwitchesInput :=
  PairSwitches.CM.connectivity_by_pair_switches

theorem properPushforward : CycleOperations.CM.Construction.FunctorialityInput :=
  Cycles.Functoriality.DimensionPreserving.Construction.cycleClass_proper_pushforward

theorem geometricPullback : CycleOperations.CM.Construction.LineBundleCyclesInput := by
  intro X Y f p
  refine ⟨Divisors.LineBundles.Geometric.CycleClass.BundleCycles.geometricCycleClassQ X p, Divisors.LineBundles.Geometric.CycleClass.BundleCycles.geometricCycleClassQ Y p,
    Divisors.LineBundles.Graph.ChowPullback.BundleCycles.graphChowPullback f p, Divisors.LineBundles.Geometric.CycleClass.BundleCycles.geometricCycleClassQ_isGeometric X p,
    Divisors.LineBundles.Geometric.CycleClass.BundleCycles.geometricCycleClassQ_isGeometric Y p, Divisors.LineBundles.Geometric.GraphPullback.BundleCycles.graphChowPullback_isGeometric f p,
    ?_, Divisors.LineBundles.Graph.ChowNaturality.BundleCycles.graphChowPullback_cycleClass f p⟩
  intro clX clY pull hX hY hpull
  exact ⟨Divisors.LineBundles.Geometric.CycleClass.BundleCycles.geometricCycleClassQ_eq_of_isGeometric X p clX hX,
    Divisors.LineBundles.Geometric.CycleClass.BundleCycles.geometricCycleClassQ_eq_of_isGeometric Y p clY hY,
    Divisors.LineBundles.Geometric.MapCharacterization.BundleCycles.isGeometricGraphPullback_unique f p pull (Divisors.LineBundles.Graph.ChowPullback.BundleCycles.graphChowPullback f p)
      hpull (Divisors.LineBundles.Geometric.GraphPullback.BundleCycles.graphChowPullback_isGeometric f p)⟩

theorem exteriorProduct : CycleOperations.CM.Construction.ExteriorInput :=
  CycleClass.Thom.Exterior.cycle_class_exterior

theorem oppositePairing : Pairing.CM.Construction.PolarizedPairingInput :=
  Analysis.HodgeTheory.PolarizedPairing.Constructions.opposite_embedding_pairing_ne_zero

theorem riemannProjectivity : CMVariety.ProjectiveTorusData.CM.Abelian.RiemannProjectivityInput :=
  Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion

theorem realization (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E] :
    ComplexMultiplication.CMKnownResults.CM.KnownResults.RiemannH1Realization E :=
  CMVariety.RiemannRealization.CM.Abelian.riemannH1Realization_of_RiemannProjectivity riemannProjectivity E

theorem fullness : ComplexMultiplication.KnownAlgebraicity.CM.KnownResults.RationalH1MapsAreAlgebraic :=
  CMVariety.Background.CM.Abelian.rationalH1MapsAreAlgebraic_of_DegreeTwo DegreeTwo.Algebraicity.CM.weight_one_algebraicity_unconditional

theorem lefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne :=
  CMVariety.Background.CM.Abelian.lefschetzOneOne_of_DegreeTwo DegreeTwo.Algebraicity.CM.degree_two_algebraicity_unconditional

theorem exterior : ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology :=
  AbelianVariety.ExteriorCohomology.CM.abelian_exterior_cohomology

theorem resolution : CMVariety.CycleResolution.CM.Abelian.ResolutionInput :=
  Resolution.Blowups.Strong.Construction.resolution_of_singularities

theorem resolutionClass : CMVariety.CycleResolution.CM.Abelian.ResolutionClassInput :=
  Cycles.Functoriality.Resolution.Construction.cycleClass_of_resolution

theorem hodgeDecomposition : CMVariety.Decomposition.CM.Abelian.HodgeDecompositionInput :=
  Analysis.HodgeTheory.Decomposition.Constructions.hodge_decomposition_and_filtration

theorem cycles : ComplexMultiplication.CMKnownResults.CM.KnownResults.CycleClassesAreHodge :=
  CMVariety.CycleClasses.CM.Abelian.cycleClassesAreHodge_of_geometric_inputs resolution resolutionClass hodgeDecomposition

theorem switches (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E] :
    Definitions.CM.FourFactorSwitchAlgebraicity E :=
  CMVariety.SwitchOf.CM.Abelian.fourFactorSwitchAlgebraicity_of_SurfaceConstruction CycleCoefficientsP.p54_input E

end AlgebraicGeometry.HodgeConjecture.CMReduction.Established

namespace AlgebraicGeometry.HodgeConjecture.CMReduction.Established.CM

/-! The CMReduction statement, with its proof supplied by the completed development. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- CMReduction: algebraicity of four-factor switches implies the CM result,
using realization, weight-one algebraicity, and exterior cohomology. -/
theorem four_factor_switches_imply_cm
    (hrealization :
      ∀ (E : IntermediateField ℚ ℂ)
        [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E],
        ComplexMultiplication.CMKnownResults.CM.KnownResults.RiemannH1Realization E)
    (hfullness : ComplexMultiplication.KnownAlgebraicity.CM.KnownResults.RationalH1MapsAreAlgebraic)
    (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (hexterior : ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology)
    (hcycles : ComplexMultiplication.CMKnownResults.CM.KnownResults.CycleClassesAreHodge)
    (hswitch :
      ∀ (E : IntermediateField ℚ ℂ)
        [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E],
        Definitions.CM.FourFactorSwitchAlgebraicity E) :
    ComplexMultiplication.CMCore.CM.cmHodgeClaim := by
  exact FourFactorSwitches.CM.Construction.four_factor_switches_imply_cm
    scalarTrace connectivity
    properPushforward geometricPullback
    exteriorProduct oppositePairing
    hrealization hfullness hlefschetz hexterior hcycles hswitch

end AlgebraicGeometry.HodgeConjecture.CMReduction.Established.CM

end

end OAI
