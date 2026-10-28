import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralMatrixUnit
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SubringBigCellDeterminant

/-! # Pivot Choices -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PivotChoices.CM

noncomputable section

/-! Local zero-one row corrections, chosen over the integer ring
where the original adelic matrix unit and its inverse are integral. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralMatrixUnit.CM

variable {I : Type*} [Fintype I]

def integralCorrection (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hA : IntegralMatrixUnit.CM.IsIntegral A v) (i : I) :
    I → v.adicCompletionIntegers ℚ :=
  (Local.MatrixPivot.CM.exists_binary_correction (IntegralMatrixUnit.CM.integralUnit A v hA) i).choose

theorem integralCorrection_spec (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hA : IntegralMatrixUnit.CM.IsIntegral A v) (i : I) :
    integralCorrection A v hA i i = 0 ∧
      (∀ j, integralCorrection A v hA i j = 0 ∨ integralCorrection A v hA i j = 1) ∧
      IsUnit ((IntegralMatrixUnit.CM.integralUnit A v hA).val i i +
        ∑ j, integralCorrection A v hA i j * (IntegralMatrixUnit.CM.integralUnit A v hA).val j i) :=
  (Local.MatrixPivot.CM.exists_binary_correction (IntegralMatrixUnit.CM.integralUnit A v hA) i).choose_spec

def fieldCorrection (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (i : I) : I → v.adicCompletion ℚ :=
  (Local.MatrixPivot.CM.exists_binary_correction (IntegralMatrixUnit.CM.localUnit A v) i).choose

theorem fieldCorrection_spec (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (i : I) :
    fieldCorrection A v i i = 0 ∧ (∀ j, fieldCorrection A v i j = 0 ∨ fieldCorrection A v i j = 1) ∧
      IsUnit ((IntegralMatrixUnit.CM.localUnit A v).val i i + ∑ j, fieldCorrection A v i j * (IntegralMatrixUnit.CM.localUnit A v).val j i) :=
  (Local.MatrixPivot.CM.exists_binary_correction (IntegralMatrixUnit.CM.localUnit A v) i).choose_spec

def correction (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (i : I) : I → v.adicCompletion ℚ :=
  if h : IntegralMatrixUnit.CM.IsIntegral A v then fun j => (integralCorrection A v h i j).val
  else fieldCorrection A v i

theorem correction_zero (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (i : I) : correction A v i i = 0 := by
  unfold correction
  split_ifs with h
  · exact congrArg Subtype.val (integralCorrection_spec A v h i).1
  · exact (fieldCorrection_spec A v i).1

theorem correction_binary (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (i j : I) :
    correction A v i j = 0 ∨ correction A v i j = 1 := by
  unfold correction
  split_ifs with h
  · exact ((integralCorrection_spec A v h i).2.1 j).imp
      (congrArg Subtype.val) (congrArg Subtype.val)
  · exact (fieldCorrection_spec A v i).2.1 j

def pivot (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (i : I) : v.adicCompletion ℚ :=
  (IntegralMatrixUnit.CM.localUnit A v).val i i + ∑ j, correction A v i j * (IntegralMatrixUnit.CM.localUnit A v).val j i

def integralPivot (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hA : IntegralMatrixUnit.CM.IsIntegral A v) (i : I) :
    v.adicCompletionIntegers ℚ :=
  (IntegralMatrixUnit.CM.integralUnit A v hA).val i i + ∑ j, integralCorrection A v hA i j * (IntegralMatrixUnit.CM.integralUnit A v hA).val j i

theorem integralPivot_map (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hA : IntegralMatrixUnit.CM.IsIntegral A v) (i : I) :
    (v.adicCompletionIntegers ℚ).subtype (integralPivot A v hA i) = pivot A v i := by
  rw [integralPivot, map_add, map_sum, pivot, correction, dite_eq_left hA]
  congr 1

theorem pivot_unit (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (i : I) : IsUnit (pivot A v i) := by
  by_cases hA : IntegralMatrixUnit.CM.IsIntegral A v
  · rw [← integralPivot_map A v hA i]
    exact (integralCorrection_spec A v hA i).2.2.map (v.adicCompletionIntegers ℚ).subtype
  · rw [pivot, correction, dite_eq_right hA]
    exact (fieldCorrection_spec A v i).2.2

theorem inverse_integral (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hA : IntegralMatrixUnit.CM.IsIntegral A v) (i : I) :
    (pivot A v i)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
  rw [← integralPivot_map A v hA i]
  exact SubringBigCellDeterminant.CM.inverse_mem (v.adicCompletionIntegers ℚ).toSubring
    (integralPivot A v hA i) (integralCorrection_spec A v hA i).2.2

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PivotChoices.CM
