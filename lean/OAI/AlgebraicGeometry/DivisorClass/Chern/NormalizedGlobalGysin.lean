import OAI.AlgebraicGeometry.DivisorClass.Chern.NormalizedLocalGysin
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularCompactGysin
import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTrace

/-! # Normalized Global Gysin -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.NormalizedGlobalGysin

noncomputable section

/-!
# ChernClass: exact adjunction and geometric trace for the assembled native Gysin map

The existing global compact Gysin map agrees with the actual normal-pair
maps after open extension. The proved normal-line coefficient removes its
scalar, so its adjunction and top trace have the original geometric
normalization. In particular, applying top Gysin to the actual proper
restriction of any compact test has the independent geometric trace.
The remaining comparison is with global multiplication by the Thom class.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularCompactGysin.Constructions
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

theorem regularCompactGysin_adjunction
    (q r : ℕ) (hs : q + r = 2 * Z.regularComplexDimension)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace) q)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) r) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (M := Z.regularAmbientSpace) r (2 * 1 + q)
      (by have h := HodgeConjecture.DegreeTwo.SourceGysinIntrinsicAdjunction.Constructions.regularSourceGysinPairingDegree V Z q r hs; omega) b
      (HodgeConjecture.DegreeTwo.RegularCompactGysin.Constructions.regularCompactGysin V Z q r hs a) =
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation Z.regularComplexDimension (M := Z.regularAnalyticSpace) r q
      (by omega)
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V Z) r b) a := by
  simp only [HodgeConjecture.DegreeTwo.RegularCompactGysin.Constructions.regularCompactGysin, LocalProductCoefficientOne.localProductCupCoefficient_line, one_smul]
  exact HodgeConjecture.DegreeTwo.IntrinsicGysinAdjunction.Constructions.nativeCompactCohomologyPushforward_adjunction
    (d := Z.regularComplexDimension) (e := V.complexDimension)
    (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V Z) q (2 * 1 + q) r hs
    (HodgeConjecture.DegreeTwo.SourceGysinIntrinsicAdjunction.Constructions.regularSourceGysinPairingDegree V Z q r hs) a b

theorem regularTopGysin_properPullback_trace
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (2 * Z.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := Z.regularAmbientSpace)
      (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularTopGysin V Z
        (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
          Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap
          (2 * Z.regularComplexDimension) b)) = Z.regularGeometricTrace b := by
  rw [HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularTopGysin_trace, LocalProductCoefficientOne.localProductCupCoefficient_line, one_mul]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.NormalizedGlobalGysin
