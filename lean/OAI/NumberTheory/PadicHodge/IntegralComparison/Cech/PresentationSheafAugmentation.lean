import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationSheafRestriction

/-! # Presentation Sheaf Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationSheafAugmentation

noncomputable section

/-! The original augmentation of a sheaf presentation resolution in degree zero. -/

open _root_.CategoryTheory

universe u v w

variable (R : Type u) [CommRing R] {C : Type v} [Category.{w} C]
  (F : Cᵒᵖ ⥤ Type u) (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{u} R)]

theorem zero : (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.sheafAugmentation R F J).f 0 =
    (presheafToSheaf J (ModuleCat.{u} R)).map ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R F).f 0) := by
  change (presheafToSheaf J (ModuleCat.{u} R)).map ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R F).f 0) ≫ 𝟙 _ = _
  exact Category.comp_id _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationSheafAugmentation
