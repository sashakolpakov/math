import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.Homogeneity

/-! # Family Identity -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FamilyIdentity.Family

/-! Evaluation of a Poincare family at its identity parameter is its original actual line class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.Homogeneity

theorem familyClass_id {S : Scheme.{u}} {B A : Over S} (P : Line.Bundles.LineBundle (B ⊗ A).left) :
    Vertical.Homogeneity.familyClass P (𝟙 B) = Line.Bundles.LineBundleClass.mk P := by
  change Line.Bundles.LineBundleClass.pullback (𝟙 B ⊗ₘ 𝟙 A).left (Line.Bundles.LineBundleClass.mk P) = _
  have h : (𝟙 B ⊗ₘ 𝟙 A).left = 𝟙 (B ⊗ A).left := by
    change (𝟙 B ⊗ₘ 𝟙 A).left = (𝟙 (B ⊗ A) : B ⊗ A ⟶ B ⊗ A).left
    simp
  rw [h, Line.Bundles.LineBundleClass.pullback_id]

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FamilyIdentity.Family
