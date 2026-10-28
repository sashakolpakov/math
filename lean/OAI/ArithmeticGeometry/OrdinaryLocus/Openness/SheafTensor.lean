import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-! # Sheaf Tensor -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafTensor.Construction

noncomputable section

/-! Tensor products of actual sheaves of modules, formed by sheafification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u

local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

local instance (X : Scheme.{u}) : SymmetricCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)

def sheafifyModule {X : Scheme.{u}} (P : X.PresheafOfModules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P

/-- Sheafifying the underlying presheaf of a module sheaf recovers it. -/
def sheafifyModuleIso {X : Scheme.{u}} (M : X.Modules) :
    sheafifyModule M.val ≅ M := by
  let c := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  have : IsIso c := by dsimp [c]; infer_instance
  exact (asIso c).app M

def sheafTensor {X : Scheme.{u}} (M N : X.Modules) : X.Modules :=
  sheafifyModule (M.val ⊗ N.val)

/-- Maps out of the sheaf tensor product are precisely maps out of the
presheaf tensor product into the target sheaf. -/
def sheafTensorHomEquiv {X : Scheme.{u}} (M N P : X.Modules) :
    (sheafTensor M N ⟶ P) ≃ (M.val ⊗ N.val ⟶ P.val) :=
  PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)

def sheafTensorCongr {X : Scheme.{u}} {M M' N N' : X.Modules}
    (e : M ≅ M') (f : N ≅ N') : sheafTensor M N ≅ sheafTensor M' N' :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (((Scheme.Modules.toPresheafOfModules X).mapIso e) ⊗ᵢ
      ((Scheme.Modules.toPresheafOfModules X).mapIso f))

def sheafTensorUnitLeft {X : Scheme.{u}} (M : X.Modules) :
    sheafTensor (LineBundle.Construction.structureSheafModule X) M ≅ M :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (λ_ M.val) ≪≫
    sheafifyModuleIso M

def sheafTensorUnitRight {X : Scheme.{u}} (M : X.Modules) :
    sheafTensor M (LineBundle.Construction.structureSheafModule X) ≅ M :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (ρ_ M.val) ≪≫
    sheafifyModuleIso M

def sheafTensorComm {X : Scheme.{u}} (M N : X.Modules) :
    sheafTensor M N ≅ sheafTensor N M :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (β_ M.val N.val)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafTensor.Construction
