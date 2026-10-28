import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.PointNormalization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison

/-! # Point Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.PointComposition

noncomputable section

/-! Restriction of the actual Poincare family is the Poincare line of the composite dual point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

variable {S : Scheme.{u}} {A : Over S} [GrpObj A] (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)
  {X T : Over S} (φ : X ⟶ D.abelian) (t : T ⟶ X)

/-- The actual product maps compose to the represented dual point. -/
theorem square : (t ⊗ₘ 𝟙 A) ≫ (φ ⊗ₘ 𝟙 A) = (t ≫ φ) ▷ A := by
  rw [tensorHom_comp_tensorHom, Category.id_comp, tensorHom_id]

/-- The line comparison is the genuine pullback-composition isomorphism. -/
def iso :
    (Scheme.Modules.pullback (t ⊗ₘ 𝟙 A).left).obj (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) φ).sheaf ≅
      (PointNormalization.line D (t ≫ φ)).sheaf :=
  (Scheme.Modules.pullbackComp (t ⊗ₘ 𝟙 A).left (φ ⊗ₘ 𝟙 A).left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (square D φ t))).app D.poincare.sheaf

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.PointComposition
