import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PivotChoices
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Units

/-! # Matrix Pivot -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MatrixPivot.CM

noncomputable section

/-! Assemble local zero-one row corrections into an adelic row
correction whose pivot is an actual unit of the finite adelic ring. -/

open scoped Classical _root_.Matrix RestrictedProduct
open Filter
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PivotChoices.CM

variable {I : Type*} [Fintype I]

def rowCorrection (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (i : I) : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := fun j =>
  ⟨fun v => PivotChoices.CM.correction A v i j, Filter.Eventually.of_forall fun v => by
    dsimp only
    rcases PivotChoices.CM.correction_binary A v i j with h | h
    · rw [h]; exact (v.adicCompletionIntegers ℚ).zero_mem
    · rw [h]; exact (v.adicCompletionIntegers ℚ).one_mem⟩

theorem rowCorrection_zero (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (i : I) : rowCorrection A i i = 0 := by
  apply DFunLike.ext
  intro v
  exact PivotChoices.CM.correction_zero A v i

def pivotValue (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (i : I) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  A.val i i + ∑ j, rowCorrection A i j * A.val j i

theorem pivotValue_eval (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (i : I) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    SymplecticLocal.CM.localEval v (pivotValue A i) = PivotChoices.CM.pivot A v i := by
  rw [pivotValue, map_add, map_sum]
  change A.val i i v + _ = (IntegralMatrixUnit.CM.localUnit A v).val i i + _
  congr 1

theorem pivotValue_unit (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (i : I) : IsUnit (pivotValue A i) := by
  apply Adelic.Units.CM.isUnit_of_local
  · intro v
    change SymplecticLocal.CM.localEval v (pivotValue A i) ≠ 0
    rw [pivotValue_eval]
    exact (PivotChoices.CM.pivot_unit A v i).ne_zero
  · filter_upwards [IntegralMatrixUnit.CM.eventually_integral A] with v hv
    change (SymplecticLocal.CM.localEval v (pivotValue A i))⁻¹ ∈ v.adicCompletionIntegers ℚ
    rw [pivotValue_eval]
    exact PivotChoices.CM.inverse_integral A v hv i

theorem exists_row_correction (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (i : I) :
    ∃ c : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf, c i = 0 ∧ IsUnit (A.val i i + ∑ j, c j * A.val j i) :=
  ⟨rowCorrection A i, rowCorrection_zero A i, pivotValue_unit A i⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MatrixPivot.CM
