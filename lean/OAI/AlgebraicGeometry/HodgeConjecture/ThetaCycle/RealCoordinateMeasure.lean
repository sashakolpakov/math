import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealModelCharts
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Real Coordinate Measure -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealCoordinateMeasure.CM

noncomputable section

/-! ThetaCycle: the explicit real/imaginary model coordinates preserve the
actual product Lebesgue measures used by the two chart integrals. -/

open _root_.MeasureTheory

theorem complex_real_coordinates_volume_preserving (p : ℕ) :
    MeasurePreserving (Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv p) := by
  have h₁ := volume_preserving_pi (fun _ : Fin p => Complex.volume_preserving_equiv_real_prod)
  have h₂ := volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin p)
  have h₃ := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin p ⊕ Fin p => ℝ)
  have h₄ := volume_measurePreserving_piCongrLeft (fun _ : Fin (2 * p) => ℝ)
    (Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexRealCoordinateIndexEquiv p)
  have h := h₄.comp (h₃.comp (h₂.comp h₁))
  convert! h using 1
  funext z i
  obtain ⟨i, rfl⟩ := (Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexRealCoordinateIndexEquiv p).surjective i
  simp only [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  cases i with
  | inl i => rw [Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv_apply_re]; rfl
  | inr i => rw [Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv_apply_im]; rfl

theorem integral_complex_real_coordinates (p : ℕ) (f : (Fin (2 * p) → ℝ) → ℂ) :
    (∫ z : Fin p → ℂ, f (Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv p z)) = ∫ y, f y :=
  (complex_real_coordinates_volume_preserving p).integral_comp
    (Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv p).toHomeomorph.measurableEmbedding f

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealCoordinateMeasure.CM
