import OAI.AlgebraicGeometry.DivisorClass.Chern.NamedLocalCrossGenerator
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality

/-! # Product Dual Evaluation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ProductDualEvaluation

noncomputable section

/-! The original coordinate-normalized dual class evaluates to one on
the existing named line–tangent cross generator. -/

open _root_.CategoryTheory _root_.HomologicalComplex OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def combinedComplexRationalDualClass (p : ℕ) :
    CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalLocalCohomology (p + 2) (2 * p + 4) := by
  simpa only [Nat.mul_succ] using CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + 2)

theorem combinedComplexRationalDualClass_evaluation (p : ℕ) :
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (Fin (p + 2) → ℂ)) ({0}ᶜ)
      (2 * p + 4) (combinedComplexRationalDualClass p) (CombinedComplexSphereMap.combinedComplexRationalGeneratorClass p) = 1 := by
  have hf := LinearMap.congr_fun (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass_functional (p + 2))
    (Rational.PositiveComplexSphere.positiveComplexOrthantRationalClass (p + 1))
  have h : CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (Fin (p + 2) → ℂ)) ({0}ᶜ)
      (2 * (p + 2)) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + 2)) (Rational.PositiveComplexSphere.positiveComplexOrthantRationalClass (p + 1)) = 1 :=
    hf.trans (Rational.PositiveComplexSphere.positiveComplexOrthantRationalClass_coordinate (p + 1))
  simpa only [combinedComplexRationalDualClass, CombinedComplexSphereMap.combinedComplexRationalGeneratorClass,
    Rational.PositiveComplexSphere.positiveComplexOrthantRationalClass, Nat.mul_succ, id_eq] using h

def lineTangentCoordinateDualClass (p : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ))) ({0}ᶜ) (2 * p + 4) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Complex.ProductFactorMaps.complexProductLineMap p)
    (Complex.ProductFactorMaps.complexProductLineMap_puncture p) (2 * p + 4) (combinedComplexRationalDualClass p)

theorem lineTangentCoordinateDualClass_evaluation (p : ℕ) :
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ))) ({0}ᶜ) (2 * p + 4)
      (lineTangentCoordinateDualClass p) (NamedLocalCrossGenerator.lineTangentCrossClass p) = 1 := by
  rw [lineTangentCoordinateDualClass, CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles.relativeHomologyEvaluation_naturality,
    NamedLocalCrossGenerator.lineTangentCrossClass_line, combinedComplexRationalDualClass_evaluation]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ProductDualEvaluation
