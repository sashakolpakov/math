import OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalLineClass
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

/-! # Diagonal Recovery -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalRecovery

noncomputable section

/-! Actual geometric recovery restricts to the diagonals of the original and quotient families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalLineClass OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {S : Scheme.{u}} {A B D : Over S}
  (f : A ⟶ B) (φ : A ⟶ D) (P : Line.Bundles.LineBundle (D ⊗ A).left)
  (R : Line.Bundles.LineBundle (B ⊗ B).left)
  (e : (Scheme.Modules.pullback (f ⊗ₘ f).left).obj R.sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)

/-- The diagonal square of an arbitrary actual quotient commutes. -/
theorem diagonal_square : f ≫ lift (𝟙 B) (𝟙 B) = lift (𝟙 A) (𝟙 A) ≫ (f ⊗ₘ f) := by
  simp

/-- The canonical Poincare parameter square restricts to the diagonal line. -/
theorem parameter_diagonal : lift (𝟙 A) (𝟙 A) ≫ (φ ⊗ₘ 𝟙 A) = lift φ (𝟙 A) := by
  simp

/-- Pulling back the quotient's actual diagonal line recovers the original Poincare diagonal. -/
def pullbackIso :
    (Scheme.Modules.pullback f.left).obj (DiagonalLineClass.diagonalLine R (𝟙 B)).sheaf ≅ (DiagonalLineClass.diagonalLine P φ).sheaf :=
  (Scheme.Modules.pullbackComp f.left (lift (𝟙 B) (𝟙 B)).left).app R.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (diagonal_square f))).app R.sheaf ≪≫
    (Scheme.Modules.pullbackComp (lift (𝟙 A) (𝟙 A)).left (f ⊗ₘ f).left).symm.app R.sheaf ≪≫
    (Scheme.Modules.pullback (lift (𝟙 A) (𝟙 A)).left).mapIso e ≪≫
    (Scheme.Modules.pullbackComp (lift (𝟙 A) (𝟙 A)).left (φ ⊗ₘ 𝟙 A).left).app P.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (parameter_diagonal φ))).app P.sheaf

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalRecovery
