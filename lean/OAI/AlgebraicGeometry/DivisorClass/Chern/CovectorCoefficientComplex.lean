import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorPairCoefficient
import OAI.Analysis.HodgeTheory.Decomposition.ComplexOperatorLift

/-! # Covector Coefficient Complex -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorCoefficientComplex

noncomputable section

/-! Complex linearity is preserved by the exact coordinate metric and the correctly ordered weak-action adjoint. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ComplexOperatorLift.Constructions

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem covectorOperatorCoordinates_complex_smul (b : Module.Basis ι ℝ E) (n : ℕ)
    (L : Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (hL : ∀ (r : ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n), L (r • a) = r • L a)
    (r : ℂ) (v : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n) :
    CovectorPairCoefficient.covectorOperatorCoordinates b n L (r • v) = r • CovectorPairCoefficient.covectorOperatorCoordinates b n L v := by
  change Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (L ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm (r • v))) =
    r • Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (L ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm v))
  rw [map_smul, hL, map_smul]

omit [FiniteDimensional ℝ E] in
theorem covectorPairCoefficient_complex_smul (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (w : ℝ) (r : ℂ) (v : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n) :
    CovectorPairCoefficient.covectorPairCoefficient b n B w (r • v) = r • CovectorPairCoefficient.covectorPairCoefficient b n B w v := by
  change w • Analysis.HodgeTheory.Decomposition.CoordinateMetric.Constructions.realMatrixOperator (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram b n B)⁻¹ (r • v) =
    r • (w • Analysis.HodgeTheory.Decomposition.CoordinateMetric.Constructions.realMatrixOperator (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram b n B)⁻¹ v)
  rw [Analysis.HodgeTheory.Decomposition.ComplexMetric.Constructions.realMatrixOperator_complex_smul, smul_comm]

theorem covectorWeakActionCoefficient_complex_smul (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (w : ℝ) (L : Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (hL : ∀ (r : ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n), L (r • a) = r • L a)
    (r : ℂ) (v : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n) :
    CovectorPairCoefficient.covectorWeakActionCoefficient b n B w L (r • v) = r • CovectorPairCoefficient.covectorWeakActionCoefficient b n B w L v := by
  change (CovectorPairCoefficient.covectorOperatorCoordinates b n L).adjoint (CovectorPairCoefficient.covectorPairCoefficient b n B w (r • v)) =
    r • (CovectorPairCoefficient.covectorOperatorCoordinates b n L).adjoint (CovectorPairCoefficient.covectorPairCoefficient b n B w v)
  rw [covectorPairCoefficient_complex_smul, Analysis.HodgeTheory.Decomposition.ComplexOperatorLift.Constructions.real_adjoint_complex_smul
    (CovectorPairCoefficient.covectorOperatorCoordinates b n L) (covectorOperatorCoordinates_complex_smul b n L hL)]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorCoefficientComplex
