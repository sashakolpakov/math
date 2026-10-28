import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticLocal
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SubringBigCellDeterminant

/-! # Big Cell Choices -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BigCellChoices.CM

noncomputable section

/-! Choose local symmetric big-cell corrections integrally whenever
the original adelic matrix is integral. Their determinant inverses
are integral at those places as well. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticLocal.CM

variable {I : Type*} [Fintype I]

def integralCorrection (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hg : SymplecticLocal.CM.IsIntegral g v) :
    Matrix I I (v.adicCompletionIntegers ℚ) := (SymplecticLocal.CM.integral_big_cell g v hg).choose

theorem integralCorrection_spec (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hg : SymplecticLocal.CM.IsIntegral g v) :
    (integralCorrection g v hg).IsSymm ∧
      IsUnit ((SymplecticLocal.CM.integralSymplectic g v hg).val.toBlocks₁₁ +
        integralCorrection g v hg * (SymplecticLocal.CM.integralSymplectic g v hg).val.toBlocks₂₁).det :=
  (SymplecticLocal.CM.integral_big_cell g v hg).choose_spec

def fieldCorrection (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : Matrix I I (v.adicCompletion ℚ) :=
  (SymplecticLocal.CM.local_big_cell g v).choose

theorem fieldCorrection_spec (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    (fieldCorrection g v).IsSymm ∧
      IsUnit ((SymplecticLocal.CM.localSymplectic g v).val.toBlocks₁₁ +
        fieldCorrection g v * (SymplecticLocal.CM.localSymplectic g v).val.toBlocks₂₁).det :=
  (SymplecticLocal.CM.local_big_cell g v).choose_spec

def correction (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : Matrix I I (v.adicCompletion ℚ) :=
  if h : SymplecticLocal.CM.IsIntegral g v then (integralCorrection g v h).map (v.adicCompletionIntegers ℚ).subtype
  else fieldCorrection g v

theorem correction_symmetric (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : (correction g v).IsSymm := by
  unfold correction
  split_ifs with h
  · exact (integralCorrection_spec g v h).1.map _
  · exact (fieldCorrection_spec g v).1

theorem correction_integral (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hg : SymplecticLocal.CM.IsIntegral g v) (i j : I) :
    correction g v i j ∈ v.adicCompletionIntegers ℚ := by
  rw [correction, dite_eq_left hg]
  exact (integralCorrection g v hg i j).property

def correctedDeterminant (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : v.adicCompletion ℚ :=
  ((SymplecticLocal.CM.localSymplectic g v).val.toBlocks₁₁ + correction g v * (SymplecticLocal.CM.localSymplectic g v).val.toBlocks₂₁).det

theorem integral_determinant_map (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hg : SymplecticLocal.CM.IsIntegral g v) :
    (v.adicCompletionIntegers ℚ).subtype
      (((SymplecticLocal.CM.integralSymplectic g v hg).val.toBlocks₁₁ + integralCorrection g v hg *
        (SymplecticLocal.CM.integralSymplectic g v hg).val.toBlocks₂₁).det) = correctedDeterminant g v := by
  rw [correctedDeterminant, correction, dite_eq_left hg]
  exact SubringBigCellDeterminant.CM.determinant_map
    (v.adicCompletionIntegers ℚ).toSubring (SymplecticLocal.CM.localSymplectic g v) hg (integralCorrection g v hg)

theorem correctedDeterminant_unit (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    IsUnit (correctedDeterminant g v) := by
  by_cases hg : SymplecticLocal.CM.IsIntegral g v
  · rw [← integral_determinant_map g v hg]
    exact (integralCorrection_spec g v hg).2.map (v.adicCompletionIntegers ℚ).subtype
  · rw [correctedDeterminant, correction, dite_eq_right hg]
    exact (fieldCorrection_spec g v).2

theorem inverse_integral (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hg : SymplecticLocal.CM.IsIntegral g v) :
    (correctedDeterminant g v)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
  rw [← integral_determinant_map g v hg]
  exact SubringBigCellDeterminant.CM.inverse_mem (v.adicCompletionIntegers ℚ).toSubring
    _ (integralCorrection_spec g v hg).2

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BigCellChoices.CM
