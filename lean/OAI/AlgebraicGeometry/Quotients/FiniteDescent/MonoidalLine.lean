import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DualEvaluationIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPullbackId

/-! # Monoidal Line -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles

noncomputable section

/-! Compare the localized monoidal structure with the concrete tensor
sheaves and structure module used for FiniteDescent line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u

attribute [local instance] SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory SheafCohomology.Projective.Monoidal.Scheme.Modules.symmetricCategory

local instance sheafMonoidal (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} X.ringCatSheaf) := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

local instance localizingMonoidal (X : Scheme.{u}) :
    (SheafCohomology.Projective.OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)).IsMonoidal :=
  SheafCohomology.Projective.OfModulesMonoidal.PresheafOfModules.instSheafificationW_isMonoidal_commRingSheaf
    X.sheaf.obj X.ringCatSheaf.property

local instance localizing (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      (SheafCohomology.Projective.OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)) :=
  SheafCohomology.Projective.OfModulesMonoidal.PresheafOfModules.instSheafificationW_isLocalization_commRingSheaf
    X.sheaf.obj X.ringCatSheaf.property

local instance sheafificationMonoidal (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).Monoidal :=
  inferInstanceAs ((Localization.Monoidal.toMonoidalCategory
    (L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
    (W := SheafCohomology.Projective.OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)) (Iso.refl _)).Monoidal)

def unitIso (X : Scheme.{u}) : (𝟙_ X.Modules) ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  SheafCohomology.Projective.Invertible.Scheme.Modules.sheafifyValIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)

def tensorIso {X : Scheme.{u}} (M N : X.Modules) : M ⊗ N ≅ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N :=
  CategoryTheory.MonoidalCategory.tensorIso
      (SheafCohomology.Projective.Invertible.Scheme.Modules.sheafifyValIso M).symm (SheafCohomology.Projective.Invertible.Scheme.Modules.sheafifyValIso N).symm ≪≫
    Functor.Monoidal.μIso (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) M.val N.val

def evaluation {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    L.sheaf ⊗ (DualLine.Construction.DualLineBundle.dual L).sheaf ≅ 𝟙_ X.Modules :=
  MonoidalLineBundles.tensorIso _ _ ≪≫ DualEvaluationIs.Construction.DualEvaluation.iso L ≪≫ (unitIso X).symm

def evaluation_swap {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    (DualLine.Construction.DualLineBundle.dual L).sheaf ⊗ L.sheaf ≅ 𝟙_ X.Modules :=
  (β_ _ _) ≪≫ evaluation L

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles
