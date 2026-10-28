import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SourcePullback
import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTrace

/-! # Source Sheaf Trace -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.SourceSheafTrace

noncomputable section

/-! Every compact test has its native proper pullback and fundamental trace under the source sheaf comparison. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def compactTestComplement {X : TopCat.{0}} [T2Space X] (K : Compacts X) : Opens X :=
  ⟨(K : Set X)ᶜ, K.isCompact.isClosed.isOpen_compl⟩

variable {X Y : TopCat.{0}} [T2Space X] [MetrizableSpace Y]
variable (f : Y ⟶ X) (hf : IsProperMap f) (K : Compacts X)

def supportedSourceCompactStagePullback (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y
        (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage f hf K : Set Y)ᶜ n :=
  HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) X (compactTestComplement K)) n ≫
    HomologicalComplex.homologyMap
      (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (⊤ : Opens X)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
        (Supported.SourcePullback.supportedSourcePullback (ModuleCat.of ℚ ℚ) f (compactTestComplement K))) n ≫
      (Supported.SourceCohomology.supportedSourceGlobalCohomologyIso f (compactTestComplement K) n).hom

theorem supportedSourceCompactStagePullback_eq_native (n : ℕ) :
    supportedSourceCompactStagePullback f hf K n =
      AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ) f hf K n :=
  Supported.SourcePullback.supportedSourcePullback_cohomology f (compactTestComplement K) n

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)

theorem regularGeometricTrace_supported_source
    (K : Compacts Z.regularAmbientSpace)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
      (2 * Z.regularComplexDimension)) :
    Z.regularGeometricTrace
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
        (TopCat.of Z.regularAmbientSpace) K (2 * Z.regularComplexDimension) b) =
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of Z.regularAnalyticSpace)
      (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage Z.regularComplementTopCatMap
        Z.isProperMap_regularComplementTopCatMap K : Set Z.regularAnalyticSpace)ᶜ
      (2 * Z.regularComplexDimension)
      (supportedSourceCompactStagePullback Z.regularComplementTopCatMap
        Z.isProperMap_regularComplementTopCatMap K (2 * Z.regularComplexDimension) b)
      (CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass Z.regularComplexDimension
        (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage Z.regularComplementTopCatMap
          Z.isProperMap_regularComplementTopCatMap K : Set Z.regularAnalyticSpace)
        (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage Z.regularComplementTopCatMap
          Z.isProperMap_regularComplementTopCatMap K).isCompact) := by
  rw [supportedSourceCompactStagePullback_eq_native]
  exact Z.regularGeometricTrace_stage K b

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.SourceSheafTrace
