import OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts

/-! # Antilinear Coefficient Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AntilinearCoefficientMap.Dolbeault

noncomputable section

/-! Antiholomorphic derivative projection commutes with genuine
continuous complex-linear maps of coefficient spaces. -/

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]

theorem complexAntilinearPart_comp_coefficients (L : F →L[ℂ] G) (D : E →L[ℝ] F) :
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E G (L.restrictScalars ℝ ∘L D) =
      L.restrictScalars ℝ ∘L Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E F D := by
  ext v
  change (1 / 2 : ℂ) • (L (D v) + Complex.I • L (D (Complex.I • v))) =
    L ((1 / 2 : ℂ) • (D v + Complex.I • D (Complex.I • v)))
  rw [L.map_smul, L.map_add, L.map_smul]

end

end OAI.AlgebraicGeometry.Comparison.Betti.AntilinearCoefficientMap.Dolbeault
