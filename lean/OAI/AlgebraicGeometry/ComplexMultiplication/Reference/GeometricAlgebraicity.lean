import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.EvenHodgeClasses
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CMDecomposition
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Core
import OAI.AlgebraicGeometry.CycleClass.Thom.GeometricTrace

/-! # Geometric Algebraicity -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GeometricAlgebraicity

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # The exact original CM Hodge classes are genuine geometric cycle classes -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]

local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X

/-- The full proved CM theorem applies to the original challenge's actual Hodge classes. -/
theorem originalHodgeClass_nativeGeometricAlgebraic (hCM : Definitions.HasComplexMultiplication X)
    (p : ℕ) (a : H^(2 * p)(X; ℚ)) (ha : a ∈ Hdg^p(X; ℚ)) :
    ∃ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle (V) p,
      (V).geometricCycleClassMap p z = (EvenHodgeClasses.originalEvenBettiBridge X p).symm a := by
  apply ((V).mem_geometricAlgebraicClasses_iff p _).mp
  have hH := EvenHodgeClasses.originalHodgeClass_native X p a ha
  by_contra hn
  have hp := ((V).rationalHodgeClass_not_geometric_algebraic_bounds p _ ⟨hH, hn⟩).2
  have he := HodgeConjecture.CMReduction.Core.cm_hodge
    (BundledAbelianBridge.originalAbelianVariety X) (CMDecomposition.originalCMInput_hasCMH1 X hCM) p hp
  apply hn
  change (V).geometricAlgebraicClasses p = (V).rationalHodgeClasses p at he
  rw [he]
  exact ((V).mem_rationalHodgeClasses p _).mpr hH

/-- These are also the actual singular-boundary extensions of normalized regular Thom classes. -/
theorem originalHodgeClass_nativeThomAlgebraic (hCM : Definitions.HasComplexMultiplication X)
    (p : ℕ) (a : H^(2 * p)(X; ℚ)) (ha : a ∈ Hdg^p(X; ℚ)) :
    ∃ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle (V) p,
      (V).rationalCycleClass p z = (EvenHodgeClasses.originalEvenBettiBridge X p).symm a := by
  rw [CycleClass.Thom.GeometricTrace.Constructions.HigherThom.rationalCycleClassMap_eq_geometric]
  exact originalHodgeClass_nativeGeometricAlgebraic X hCM p a ha

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GeometricAlgebraicity
