import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClass
import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTraceMeaning

/-! # Geometric Cycle Class Meaning -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClassMeaning.DimensionCycleSupport

noncomputable section

/-!
# Geometric cycle classes and actual compact fundamental traces

These characterizations combine the proved all-tests Poincare/UCT
description with the actual proper relative pushforward of the regular
locus's integral fundamental class. No comparison to a supported Thom
class is involved.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- Every compact-stage evaluation of the geometric class is evaluation
on the actual proper relative push of an integral compact fundamental class. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.geometricCycleClass_compactStage_integralPushforward
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (K : Compacts Z.regularAmbientSpace)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
      (2 * Z.regularComplexDimension)) :
    Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (p + p) (2 * Z.regularComplexDimension)
        Z.regularGeometricTrace_degree
        (Z.regularAmbientCohomologyRestriction (p + p) Z.geometricCycleClass)
        (Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) K (2 * Z.regularComplexDimension) b) =
      Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of Z.regularAmbientSpace)
        (K : Set Z.regularAmbientSpace)ᶜ (2 * Z.regularComplexDimension) b
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap Z.regularComplementTopCatMap
          (A := (Z.regularCompactPreimage (K : Set Z.regularAmbientSpace))ᶜ)
          (B := (K : Set Z.regularAmbientSpace)ᶜ) (fun _ hx => hx)
          (2 * Z.regularComplexDimension)
          (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass Z.regularComplexDimension
            (Z.regularCompactPreimage (K : Set Z.regularAmbientSpace))
            (Z.isCompact_regularCompactPreimage (K : Set Z.regularAmbientSpace)
              K.isCompact))) := by
  rw [Z.geometricCycleClass_evaluation]
  exact Z.regularGeometricTrace_stage_pushforward K b

/-- The equivalent compact-stage formula uses the actual rational locally
finite fundamental class and its genuine proper compact trace. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.geometricCycleClass_compactStage_nativeCompactTrace
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (K : Compacts Z.regularAmbientSpace)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
      (2 * Z.regularComplexDimension)) :
    Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (p + p) (2 * Z.regularComplexDimension)
        Z.regularGeometricTrace_degree
        (Z.regularAmbientCohomologyRestriction (p + p) Z.geometricCycleClass)
        (Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) K (2 * Z.regularComplexDimension) b) =
      AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of Z.regularAmbientSpace)
        (K : Set Z.regularAmbientSpace)ᶜ (2 * Z.regularComplexDimension) b
        (AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace.Cycles.properLocallyFiniteCompactTrace ℚ Z.regularComplementTopCatMap
          Z.isProperMap_regularComplementTopCatMap (K : Set Z.regularAmbientSpace)
          K.isCompact (2 * Z.regularComplexDimension)
          Z.regularRationalLocallyFiniteFundamentalClass) := by
  rw [Z.geometricCycleClass_evaluation]
  exact Z.regularGeometricTrace_stage_nativeCompactTrace K b

/-- The actual proper compact traces determine the geometric class on
the whole projective variety, including across the singular boundary. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.eq_geometricCycleClass_iff_compactTrace
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (a : V.rationalCohomology (p + p)) :
    a = Z.geometricCycleClass ↔
      ∀ (K : Compacts Z.regularAmbientSpace)
        (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
          (2 * Z.regularComplexDimension)),
        Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (p + p)
            (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree
            (Z.regularAmbientCohomologyRestriction (p + p) a)
            (Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
              (TopCat.of Z.regularAmbientSpace) K (2 * Z.regularComplexDimension) b) =
          AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of Z.regularAmbientSpace)
            (K : Set Z.regularAmbientSpace)ᶜ (2 * Z.regularComplexDimension) b
            (AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace.Cycles.properLocallyFiniteCompactTrace ℚ Z.regularComplementTopCatMap
              Z.isProperMap_regularComplementTopCatMap (K : Set Z.regularAmbientSpace)
              K.isCompact (2 * Z.regularComplexDimension)
              Z.regularRationalLocallyFiniteFundamentalClass) := by
  constructor
  · rintro rfl
    exact Z.geometricCycleClass_compactStage_nativeCompactTrace
  · intro ha
    apply Z.geometricCycleClass_unique a
    intro b
    obtain ⟨K, c, rfl⟩ := Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_exists_stage (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (2 * Z.regularComplexDimension) b
    exact (ha K c).trans (Z.regularGeometricTrace_stage_nativeCompactTrace K c).symm

/-- Equivalently, the characterization can be stated entirely using the
actual integral compact fundamental class and its relative pushforward. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.eq_geometricCycleClass_iff_compactIntegralTrace
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (a : V.rationalCohomology (p + p)) :
    a = Z.geometricCycleClass ↔
      ∀ (K : Compacts Z.regularAmbientSpace)
        (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
          (2 * Z.regularComplexDimension)),
        Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (p + p)
            (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree
            (Z.regularAmbientCohomologyRestriction (p + p) a)
            (Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
              (TopCat.of Z.regularAmbientSpace) K (2 * Z.regularComplexDimension) b) =
          Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of Z.regularAmbientSpace)
            (K : Set Z.regularAmbientSpace)ᶜ (2 * Z.regularComplexDimension) b
            (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap Z.regularComplementTopCatMap
              (A := (Z.regularCompactPreimage (K : Set Z.regularAmbientSpace))ᶜ)
              (B := (K : Set Z.regularAmbientSpace)ᶜ) (fun _ hx => hx)
              (2 * Z.regularComplexDimension)
              (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass Z.regularComplexDimension
                (Z.regularCompactPreimage (K : Set Z.regularAmbientSpace))
                (Z.isCompact_regularCompactPreimage (K : Set Z.regularAmbientSpace)
                  K.isCompact))) := by
  constructor
  · rintro rfl
    exact Z.geometricCycleClass_compactStage_integralPushforward
  · intro ha
    apply Z.geometricCycleClass_unique a
    intro b
    obtain ⟨K, c, rfl⟩ := Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_exists_stage (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (2 * Z.regularComplexDimension) b
    exact (ha K c).trans (Z.regularGeometricTrace_stage_pushforward K c).symm

end

end OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClassMeaning.DimensionCycleSupport
