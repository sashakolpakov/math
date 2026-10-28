import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalTrace
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.CompactProperCup

/-! # Trace -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.Trace

noncomputable section

/-! The canonical Thom class of an actual closed complex immersion has the
independent source fundamental trace on every compactly supported test. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizedLocalTrace.Constructions
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.Construction

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (D : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)

/-- Pull back compact tests by the actual proper immersion and evaluate on
the independently constructed canonical fundamental class of the source. -/
def fundamentalTrace :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (2 * D.regularComplexDimension) ⟶ ModuleCat.of ℚ ℚ :=
  AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
    D.isProperMap_regularComplementTopCatMap (2 * D.regularComplexDimension) ≫
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace D.regularComplexDimension (M := D.regularAnalyticSpace)

theorem regularThomClass_fundamentalTrace [SecondCountableTopology D.regularAnalyticSpace]
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (2 * D.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (2 * p) (2 * D.regularComplexDimension)
      (NormalSourceTrace.Constructions.Construction.regularSourceGysinTopDegree V D)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (D.regularThomComplementOpen : Set D.regularAmbientSpace) (2 * p) D.regularThomClass) b =
      fundamentalTrace D b := by
  obtain ⟨a, ha⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (D.regularThomComplementOpen : Set D.regularAmbientSpace)) (2 * p) D.regularThomClass
  have hc := NormalizedLocalTrace.Constructions.compactCohomologyLeftCup_even_trace V.complexDimension p (M := D.regularAmbientSpace)
    (2 * D.regularComplexDimension) (NormalSourceTrace.Constructions.Construction.regularSourceGysinTopDegree V D)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (D.regularThomComplementOpen : Set D.regularAmbientSpace) (2 * p) D.regularThomClass) b
  have hcup := ConcreteCategory.congr_hom
    (CompactProperCup.Constructions.Construction.regularSourceCompactThomPushforward_properPullback D a ha (2 * D.regularComplexDimension)) b
  change SourceCompactPushforward.Constructions.Construction.regularSourceCompactThomPushforward D a ha (2 * D.regularComplexDimension)
    (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
      D.isProperMap_regularComplementTopCatMap (2 * D.regularComplexDimension) b) =
    HodgeConjecture.DegreeTwo.CompactLeftCup.Constructions.compactCohomologyLeftCup (TopCat.of D.regularAmbientSpace) (2 * p) (2 * D.regularComplexDimension)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (D.regularThomComplementOpen : Set D.regularAmbientSpace) (2 * p) D.regularThomClass) b at hcup
  rw [← hcup] at hc
  exact hc.symm.trans (GlobalTrace.Constructions.Construction.regularSourceCompactThomPushforward_trace D a ha
    (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
      D.isProperMap_regularComplementTopCatMap (2 * D.regularComplexDimension) b))

end Constructions.Construction

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.Trace
