import OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContraction
import OAI.Analysis.DifferentialForms.Manifold.DolbeaultLocal

/-! # Dolbeault Contraction Algebra -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.DolbeaultContractionAlgebra

noncomputable section

/-! The actual algebraic Cartan cancellation for the antiholomorphic
derivative, obtained from alternating covectors and coefficient contraction. -/

open _root_.ContinuousAlternatingMap

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem covectorContraction_derivative (n : ℕ) (v : E)
    (D : E →L[ℝ] E [⋀^Fin (n + 1)]→L[ℝ] ℂ) :
    (AntiholomorphicContraction.Dolbeault.covectorContraction n v).restrictScalars ℝ ∘L D = AlgebraicTopology.DeRham.Comparison.RadialOne.contractionDerivative D v := by
  ext u w
  rfl

theorem covectorContraction_antilinearPart (n : ℕ) (v : E)
    (D : E →L[ℝ] E [⋀^Fin (n + 1)]→L[ℝ] ℂ) :
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (E [⋀^Fin n]→L[ℝ] ℂ)
        ((AntiholomorphicContraction.Dolbeault.covectorContraction n v).restrictScalars ℝ ∘L D) =
      (AntiholomorphicContraction.Dolbeault.covectorContraction n v).restrictScalars ℝ ∘L
        Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (E [⋀^Fin (n + 1)]→L[ℝ] ℂ) D := by
  ext u w
  rfl

theorem dolbeault_covectorContraction_add (n : ℕ) (v : E)
    (D : E →L[ℝ] E [⋀^Fin (n + 1)]→L[ℝ] ℂ) :
    alternatizeUncurryFin
        (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (E [⋀^Fin n]→L[ℝ] ℂ)
          ((AntiholomorphicContraction.Dolbeault.covectorContraction n v).restrictScalars ℝ ∘L D)) +
      AntiholomorphicContraction.Dolbeault.covectorContraction (n + 1) v
        (alternatizeUncurryFin
          (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (E [⋀^Fin (n + 1)]→L[ℝ] ℂ) D)) =
      Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (E [⋀^Fin (n + 1)]→L[ℝ] ℂ) D v := by
  rw [covectorContraction_antilinearPart, covectorContraction_derivative]
  exact AlgebraicTopology.DeRham.Comparison.RadialOne.alternatize_contractionDerivative_add _ v

end

end OAI.AlgebraicGeometry.Comparison.Betti.DolbeaultContractionAlgebra
