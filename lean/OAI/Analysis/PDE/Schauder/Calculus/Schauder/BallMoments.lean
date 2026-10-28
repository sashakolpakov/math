import OAI.Analysis.PDE.Schauder.Calculus.Schauder.RadialFlux

/-! Radial quadratic moments on a ball. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

def ballWeight (ρ : ℝ → ℝ) (R t : ℝ) : ℝ := (Iio R).indicator ρ t

variable {m : ℕ}

theorem ballWeight_integral (ρ : ℝ → ℝ) (R : ℝ) (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    (∫ y, ballWeight ρ R ‖y‖ * f y) = ∫ y in ball 0 R, ρ ‖y‖ * f y := by
  rw [← integral_indicator measurableSet_ball]
  congr 1
  funext y
  by_cases hy : ‖y‖ < R <;> simp [ballWeight, hy]

theorem ballMoment_offDiagonal (ρ : ℝ → ℝ) (R : ℝ) (i j : Fin m) (hij : i ≠ j) :
    (∫ y in ball 0 R, ρ ‖y‖ * (y : EuclideanSpace ℝ (Fin m)) i * y j) = 0 := by
  have h := radialMoment_offDiagonal (ballWeight ρ R) i j hij
  simpa only [radialMoment, mul_assoc, ballWeight_integral] using h

theorem ballMoment_diagonal_eq (ρ : ℝ → ℝ) (R : ℝ) (i j : Fin m) :
    (∫ y in ball 0 R, ρ ‖y‖ * (y : EuclideanSpace ℝ (Fin m)) i * y i) =
      ∫ y in ball 0 R, ρ ‖y‖ * (y : EuclideanSpace ℝ (Fin m)) j * y j := by
  have h := radialMoment_diagonal_eq (ballWeight ρ R) i j
  simpa only [radialMoment, mul_assoc, ballWeight_integral] using h

end OAI.Analysis.PDE.Schauder
