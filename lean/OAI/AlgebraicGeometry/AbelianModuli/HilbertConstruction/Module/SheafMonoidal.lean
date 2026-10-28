/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorLocalizationAssembly
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Localization.Monoidal.Braided

/-! # Sheaf Monoidal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SheafMonoidal

noncomputable section

/-! The actual category of module sheaves carries the symmetric tensor structure induced by sheafification. -/

universe v v' u u'

open _root_.CategoryTheory MonoidalCategory _root_.PresheafOfModules

namespace SheafTensorLocalization

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  (S : Cᵒᵖ ⥤ CommRingCat.{u})
  (hS : Presheaf.IsSheaf J (S ⋙ forget₂ CommRingCat RingCat))

instance instSheafificationW_isLocalization_commRingSheaf :
    (sheafification.{u}
        (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)).IsLocalization
      (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW.{u}
        (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)) :=
  SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW_isLocalization _

instance instSheafificationW_isMonoidal_commRingSheaf :
    (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW.{u}
      (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)).IsMonoidal :=
  HilbertConstruction.Sheaf.TensorLocalizationAssembly.SheafTensorLocalization.sheafificationW_isMonoidal _

@[implicit_reducible]
def sheafOfModulesMonoidalCategory :
    MonoidalCategory (SheafOfModules.{u} (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})) :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal
    (L := sheafification.{u} (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
    (W := SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW.{u} (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
    (Iso.refl _)))

@[implicit_reducible]
def sheafOfModulesSymmetricCategory :
    letI := sheafOfModulesMonoidalCategory S hS
    SymmetricCategory (SheafOfModules.{u} (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})) :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal
    (L := sheafification.{u} (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
    (W := SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW.{u} (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
    (Iso.refl _)))

end SheafTensorLocalization

open _root_.AlgebraicGeometry

@[implicit_reducible]
def moduleMonoidalCategory (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafTensorLocalization.sheafOfModulesMonoidalCategory X.sheaf.obj X.ringCatSheaf.property

@[implicit_reducible]
def moduleSymmetricCategory (X : Scheme.{u}) :
    letI := moduleMonoidalCategory X
    SymmetricCategory X.Modules :=
  SheafTensorLocalization.sheafOfModulesSymmetricCategory X.sheaf.obj X.ringCatSheaf.property

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SheafMonoidal
