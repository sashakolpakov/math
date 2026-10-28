import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomTopIntrinsic
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomProperCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactLeftCupTrace
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicGysinTopTrace

/-! # Compact Thom Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomTrace.Constructions

noncomputable section

/-! The global supported Thom class has the independently constructed regular geometric trace on every compact test, up to the proved product coefficient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceCompactThomPushforward_trace
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (2*Z.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := Z.regularAmbientSpace)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace))
        Z.regularGeometricTrace_degree)
        (CompactThomZero.Constructions.regularSourceCompactThomPushforward Z a ha (2*Z.regularComplexDimension) b)) =
    LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension *
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension (M := Z.regularAnalyticSpace) b := by
  rw [CompactThomTopIntrinsic.Constructions.regularSourceCompactThomPushforward_top_eq_native Z a ha]
  change AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := Z.regularAmbientSpace)
    (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace))
      Z.regularGeometricTrace_degree)
      (LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension •
        IntrinsicGysinAdjunction.Constructions.nativeCompactCohomologyPushforward (d := Z.regularComplexDimension) (e := V.complexDimension)
          (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) (2*Z.regularComplexDimension) (2+2*Z.regularComplexDimension) 0 rfl
          (SourceGysinIntrinsicAdjunction.Constructions.regularSourceGysinPairingDegree V Z (2*Z.regularComplexDimension) 0 rfl) b)) = _
  rw [map_smul, map_smul]
  exact congrArg (fun z => LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension * z)
    (IntrinsicGysinTopTrace.Constructions.nativeCompactCohomologyPushforward_top_trace (d := Z.regularComplexDimension) (e := V.complexDimension)
      (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) (2+2*Z.regularComplexDimension)
      (SourceGysinIntrinsicAdjunction.Constructions.regularSourceGysinPairingDegree V Z (2*Z.regularComplexDimension) 0 rfl) Z.regularGeometricTrace_degree b)

theorem regularThomClass_geometric_evaluation
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      (2*Z.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension 2 (2*Z.regularComplexDimension) Z.regularGeometricTrace_degree
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) 2 Z.regularThomClass) b =
    LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension * Z.regularGeometricTrace b := by
  obtain ⟨a, ha⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2 Z.regularThomClass
  let c := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
    (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) 2 Z.regularThomClass
  let F := fun z => AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := Z.regularAmbientSpace)
    (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace))
      Z.regularGeometricTrace_degree) z)
  have hc := CompactLeftCupTrace.Constructions.compactCohomologyLeftTwoCup_trace V.complexDimension
    (2*Z.regularComplexDimension) Z.regularGeometricTrace_degree c b
  have hp := ConcreteCategory.congr_hom
    (CompactThomProperCup.Constructions.regularSourceCompactThomPushforward_properPullback Z a ha (2*Z.regularComplexDimension)) b
  have ht := regularSourceCompactThomPushforward_trace Z a ha
    (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap (2*Z.regularComplexDimension) b)
  exact hc.symm.trans ((congrArg F hp.symm).trans ht)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomTrace.Constructions
