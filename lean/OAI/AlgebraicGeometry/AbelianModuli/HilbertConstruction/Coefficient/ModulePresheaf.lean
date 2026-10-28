import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.RingModulePresheaf
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Module Presheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf

noncomputable section

/-! Module sections with coefficients in a chosen base ring satisfy the sheaf condition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

def coefficientModulePresheaf (f : R →+* Γ(X, ⊤)) (M : X.Modules) :
    TopCat.Presheaf (ModuleCat R) X :=
  Global.RingModulePresheaf.globalRingModulePresheaf M ⋙ ModuleCat.restrictScalars f

theorem coefficientModulePresheaf_isSheaf (f : R →+* Γ(X, ⊤)) (M : X.Modules) :
    (coefficientModulePresheaf f M).IsSheaf :=
  CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf _ _ (ModuleCat.restrictScalars f)
    (Global.RingModulePresheaf.globalRingModulePresheaf_isSheaf M)

def schemeCoefficientMap (p : X ⟶ Spec (.of R)) : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop).hom

def schemeModulePresheaf (p : X ⟶ Spec (.of R)) (M : X.Modules) :
    TopCat.Presheaf (ModuleCat R) X :=
  coefficientModulePresheaf (schemeCoefficientMap p) M

theorem schemeModulePresheaf_isSheaf (p : X ⟶ Spec (.of R)) (M : X.Modules) :
    (schemeModulePresheaf p M).IsSheaf :=
  coefficientModulePresheaf_isSheaf (schemeCoefficientMap p) M

def coefficientPairwiseLimit (f : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    IsLimit ((coefficientModulePresheaf f M).mapCone (Pairwise.cocone U).op) :=
  Classical.choice ((coefficientModulePresheaf_isSheaf f M).isSheafPairwiseIntersections U)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf
