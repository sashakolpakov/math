import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

/-! # Family Recovery -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FamilyRecovery.Family

noncomputable section

/-! Actual recovery of a product line gives the Picard pullback equation on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.Homogeneity

variable {S : Scheme.{u}} {A B X Y Z : Over S}
  (f : A ⟶ B) (g : X ⟶ Y)
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (R : Line.Bundles.LineBundle (B ⊗ Y).left)
  (e : (Scheme.Modules.pullback (f ⊗ₘ g).left).obj R.sheaf ≅ L.sheaf)

include e

/-- A genuine product-square recovery gives the equality of relative line classes at every point. -/
theorem familyClass_recovery {T : Over S} (x : T ⟶ A) :
    Line.Bundles.LineBundleClass.pullback (Functor.familyMap g T) (Vertical.Homogeneity.familyClass R (x ≫ f)) = Vertical.Homogeneity.familyClass L x := by
  change Line.Bundles.LineBundleClass.pullback (𝟙 T ⊗ₘ g).left
      (Line.Bundles.LineBundleClass.pullback ((x ≫ f) ⊗ₘ 𝟙 Y).left (Line.Bundles.LineBundleClass.mk R)) =
    Line.Bundles.LineBundleClass.pullback (x ⊗ₘ 𝟙 X).left (Line.Bundles.LineBundleClass.mk L)
  rw [← Line.Bundles.LineBundleClass.pullback_comp]
  have hs : (𝟙 T ⊗ₘ g).left ≫ ((x ≫ f) ⊗ₘ 𝟙 Y).left =
      (x ⊗ₘ 𝟙 X).left ≫ (f ⊗ₘ g).left :=
    congrArg Over.Hom.left (by
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      simp : (𝟙 T ⊗ₘ g) ≫ ((x ≫ f) ⊗ₘ 𝟙 Y) = (x ⊗ₘ 𝟙 X) ≫ (f ⊗ₘ g))
  rw [hs, Line.Bundles.LineBundleClass.pullback_comp]
  have he : Line.Bundles.LineBundleClass.pullback (f ⊗ₘ g).left (Line.Bundles.LineBundleClass.mk R) = Line.Bundles.LineBundleClass.mk L :=
    Quotient.sound ⟨e⟩
  rw [he]

omit e in
/-- Evaluation of an actual pulled-back family is evaluation at the composed parameter. -/
theorem familyClass_familyLine (P : Line.Bundles.LineBundle (Z ⊗ X).left) (φ : A ⟶ Z)
    {T : Over S} (x : T ⟶ A) :
    Vertical.Homogeneity.familyClass (FirstBiextensionFactor.familyLine P φ) x = Vertical.Homogeneity.familyClass P (x ≫ φ) := by
  change Line.Bundles.LineBundleClass.pullback (x ⊗ₘ 𝟙 X).left
      (Line.Bundles.LineBundleClass.pullback (φ ⊗ₘ 𝟙 X).left (Line.Bundles.LineBundleClass.mk P)) = _
  rw [← Line.Bundles.LineBundleClass.pullback_comp]
  have hs : (x ⊗ₘ 𝟙 X).left ≫ (φ ⊗ₘ 𝟙 X).left = ((x ≫ φ) ⊗ₘ 𝟙 X).left :=
    congrArg Over.Hom.left (by simp : (x ⊗ₘ 𝟙 X) ≫ (φ ⊗ₘ 𝟙 X) = (x ≫ φ) ⊗ₘ 𝟙 X)
  rw [hs]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FamilyRecovery.Family
