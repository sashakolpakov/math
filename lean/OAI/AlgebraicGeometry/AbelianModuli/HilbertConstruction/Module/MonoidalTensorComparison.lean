import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SheafMonoidal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf

/-! # Monoidal Tensor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MonoidalTensorComparison

noncomputable section

/-! The symmetric tensor structure on module sheaves agrees with HilbertConstruction's actual sheafified tensor product and structure module. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SheafMonoidal.SheafTensorLocalization

local instance (X : Scheme.{u}) : MonoidalCategory X.Modules := SheafMonoidal.moduleMonoidalCategory X

local instance (X : Scheme.{u}) : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

local instance (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW (𝟙 X.ringCatSheaf.obj)) := SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW_isLocalization _

local instance (X : Scheme.{u}) : (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW (𝟙 X.ringCatSheaf.obj)).IsMonoidal :=
  SheafMonoidal.SheafTensorLocalization.instSheafificationW_isMonoidal_commRingSheaf X.sheaf.obj X.ringCatSheaf.property

def moduleSheafifyValIso {X : Scheme.{u}} (M : SheafOfModules X.ringCatSheaf) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M.val ≅ M :=
  (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app M

def moduleMonoidalUnitIso (X : Scheme.{u}) : 𝟙_ X.Modules ≅ Line.Bundles.structureModule X :=
  moduleSheafifyValIso (Line.Bundles.structureModule X)

def moduleMonoidalTensorIso {X : Scheme.{u}} (M N : X.Modules) : M ⊗ N ≅ Tensor.ProductSheaf.tensorModule M N :=
  ((moduleSheafifyValIso M).symm ⊗ᵢ (moduleSheafifyValIso N).symm) ≪≫
    Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW (𝟙 X.ringCatSheaf.obj)) (Iso.refl _) M.val N.val

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MonoidalTensorComparison
