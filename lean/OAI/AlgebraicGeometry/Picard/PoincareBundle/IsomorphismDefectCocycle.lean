import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios

/-! # Isomorphism Defect Cocycle -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphismDefectCocycle

noncomputable section

/-! Associativity of actual line isomorphisms forces the composition-defect cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios

variable {X : Scheme.{u}} {M₀ M₁ M₂ M₃ : X.Modules}

/-- The four triangular defects of a tetrahedron satisfy the cocycle identity.
All coefficients are extracted from actual sheaf isomorphisms. -/
theorem cocycle (h₀ : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M₀) (h₁ : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M₁)
    (e₀₁ : M₀ ≅ M₁) (e₁₂ : M₁ ≅ M₂) (e₂₃ : M₂ ≅ M₃)
    (e₀₂ : M₀ ≅ M₂) (e₁₃ : M₁ ≅ M₃) (e₀₃ : M₀ ≅ M₃) :
    Line.IsoRatios.ratio h₀ (e₀₁ ≪≫ e₁₂) e₀₂ * Line.IsoRatios.ratio h₀ (e₀₂ ≪≫ e₂₃) e₀₃ =
      Line.IsoRatios.ratio h₁ (e₁₂ ≪≫ e₂₃) e₁₃ * Line.IsoRatios.ratio h₀ (e₀₁ ≪≫ e₁₃) e₀₃ := by
  have hleft := Line.IsoRatios.ratio_chain h₀ ((e₀₁ ≪≫ e₁₂) ≪≫ e₂₃) (e₀₂ ≪≫ e₂₃) e₀₃
  rw [Line.IsoRatios.ratio_postcomp] at hleft
  have hright := Line.IsoRatios.ratio_chain h₀ (e₀₁ ≪≫ (e₁₂ ≪≫ e₂₃)) (e₀₁ ≪≫ e₁₃) e₀₃
  rw [Line.IsoRatios.ratio_precomp h₁ h₀ e₀₁] at hright
  rw [Iso.trans_assoc] at hleft
  exact hleft.trans hright.symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphismDefectCocycle
