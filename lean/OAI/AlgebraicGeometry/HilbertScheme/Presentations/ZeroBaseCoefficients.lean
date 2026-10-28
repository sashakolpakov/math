import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AffineCoefficientProperty

/-! # Zero Base Coefficients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ZeroBaseCoefficients

noncomputable section

/-! The coefficient property over a zero ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem properAffineCoefficientProperty_zero (R : CommRingCat.{u}) [Subsingleton R] :
    Proper.AffineCoefficientProperty.ProperAffineCoefficientProperty R := by
  intro X f _ _ K
  refine ⟨⊥, fun J => ⟨fun _ => bot_le, fun _ => ?_⟩⟩
  have hJ : J = ⊤ := Subsingleton.elim _ _
  rw [hJ, OrderIso.map_top, Scheme.IdealSheafData.comap_top]
  exact le_top

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ZeroBaseCoefficients
