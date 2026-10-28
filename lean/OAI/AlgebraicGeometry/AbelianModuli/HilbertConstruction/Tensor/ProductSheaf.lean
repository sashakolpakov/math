import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-! # Product Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf

noncomputable section

/-!
Actual tensor products of module sheaves, obtained by sheafifying the
pointwise tensor product of the underlying module presheaves. Their universal
property follows from the proved sheafification adjunction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory

universe u

variable {X : Scheme.{u}}

local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

local instance (X : Scheme.{u}) : SymmetricCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)

/-- The tensor product of two actual module sheaves. -/
def tensorModule (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val)

/-- Morphisms out of the tensor sheaf are natural bilinear maps on sections,
encoded by the pointwise tensor product of presheaves. -/
def tensorModuleHomEquiv (M N P : X.Modules) :
    (tensorModule M N ⟶ P) ≃
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val ⟶ P.val) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ P

/-- Tensoring with the structure sheaf gives back the original module sheaf. -/
def tensorModuleUnitLeftIso (M : X.Modules) :
    tensorModule (Line.Bundles.structureModule X) M ≅ M := by
  have : IsIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit := inferInstance
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app M

/-- The tensor product of sheaves is symmetric. -/
def tensorModuleCommIso (M N : X.Modules) : tensorModule M N ≅ tensorModule N M :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (CategoryTheory.BraidedCategory.braiding M.val N.val)

/-- Isomorphisms of both factors induce an isomorphism of their tensor sheaves. -/
def tensorModuleCongr {M M' N N' : X.Modules} (e : M ≅ M') (f : N ≅ N') :
    tensorModule M N ≅ tensorModule M' N' :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    ((Scheme.Modules.toPresheafOfModules X).mapIso e ⊗ᵢ
      (Scheme.Modules.toPresheafOfModules X).mapIso f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf
