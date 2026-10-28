import OAI.AlgebraicGeometry.Picard.PoincareBundle.FamilyRecovery
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Homomorphism

/-! # Family Map -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.FamilyMap.Family

noncomputable section

/-! A pulled-back universal Poincare family represents its actual parameter morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {S : Scheme.{u}} {A X Z : Over S} [GrpObj X]
  (P : Line.Bundles.LineBundle (Z ⊗ X).left) (φ : A ⟶ Z)
  (βP : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber P (Vertical.ProductParameters.inputLeft Z X)) (Line.Fibers.fiber P (Vertical.ProductParameters.inputRight Z X))
    (Line.Fibers.fiber P (Vertical.ProductParameters.outputPoint Z X))) (hβP : IsIso (Bilinear.BilinearPullback.toHom βP))
  (βF : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber (FirstBiextensionFactor.familyLine P φ) (Vertical.ProductParameters.inputLeft A X))
    (Line.Fibers.fiber (FirstBiextensionFactor.familyLine P φ) (Vertical.ProductParameters.inputRight A X)) (Line.Fibers.fiber (FirstBiextensionFactor.familyLine P φ) (Vertical.ProductParameters.outputPoint A X)))
  (hβF : IsIso (Bilinear.BilinearPullback.toHom βF))

/-- Pulling back the universal family composes its actual homogeneous presheaf parameter. -/
theorem homogeneousClass_familyLine {T : Over S} (x : T ⟶ A) :
    Map.homogeneousClass (FirstBiextensionFactor.familyLine P φ) βF hβF x = Map.homogeneousClass P βP hβP (x ≫ φ) := by
  apply Subtype.ext
  exact FamilyRecovery.Family.familyClass_familyLine P φ x

/-- The same composition equation holds in the homogeneous Picard sheaf. -/
theorem sectionClass_familyLine {T : Over S} (x : T ⟶ A) :
    Map.sectionClass (FirstBiextensionFactor.familyLine P φ) βF hβF x = Map.sectionClass P βP hβP (x ≫ φ) :=
  congrArg ((toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf X)).app (op T))
    (homogeneousClass_familyLine P φ βP hβP βF hβF x)

/-- The genuine universal property recovers the original morphism from its pulled-back Poincare line. -/
theorem representedMap_familyLine (HP : (Homogeneous.homogeneousSheaf X).obj.RepresentableBy Z)
    (hP : HP.homEquiv (𝟙 Z) = Map.sectionClass P βP hβP (𝟙 Z)) :
    Map.representedMap (FirstBiextensionFactor.familyLine P φ) βF hβF HP = φ := by
  apply HP.homEquiv.injective
  have hs := sectionClass_familyLine P φ βP hβP βF hβF (𝟙 A)
  rw [Category.id_comp] at hs
  exact (Equiv.apply_symm_apply _ _).trans
    (hs.trans (Homomorphism.universalSection_action P βP hβP HP hP φ).symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.FamilyMap.Family
