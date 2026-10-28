import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.AlgebraPresheaf
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Algebra Section Modules -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSectionModules

noncomputable section

/-! The underlying coefficient modules of the structure sheaf and their finite limits. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

def commAlgToModules (R : Type u) [CommRing R] : CommAlgCat.{u} R ⥤ ModuleCat.{u} R :=
  forget₂ (CommAlgCat R) (AlgCat R) ⋙ forget₂ (AlgCat R) (ModuleCat R)

def algebraSectionModulePresheaf (f : R →+* Γ(X, ⊤)) :
    TopCat.Presheaf (ModuleCat.{u} R) X :=
  Coefficient.AlgebraPresheaf.coefficientAlgebraPresheaf f ⋙ commAlgToModules R

def algebraSectionModuleForgetIso (f : R →+* Γ(X, ⊤)) :
    algebraSectionModulePresheaf f ⋙ forget₂ (ModuleCat R) AddCommGrpCat ≅
      (Line.Bundles.structureModule X).presheaf :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro U V h; ext r; rfl)

theorem algebraSectionModulePresheaf_isSheaf (f : R →+* Γ(X, ⊤)) :
    (algebraSectionModulePresheaf f).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
    (forget₂ (ModuleCat R) AddCommGrpCat) (algebraSectionModulePresheaf f)).mpr
  exact (TopCat.Presheaf.isSheaf_iso_iff (algebraSectionModuleForgetIso f)).mpr
    (Line.Bundles.structureModule X).isSheaf

def algebraSectionPairwiseLimit (f : R →+* Γ(X, ⊤))
    {ι : Type u} (U : ι → X.Opens) :
    IsLimit ((algebraSectionModulePresheaf f).mapCone (Pairwise.cocone U).op) :=
  Classical.choice ((algebraSectionModulePresheaf_isSheaf f).isSheafPairwiseIntersections U)

def flatTensorAlgebraSectionPairwiseLimit (f : R →+* Γ(X, ⊤))
    (N : ModuleCat.{u} R) [Module.Flat R N] {ι : Type u} [Finite ι] (U : ι → X.Opens) :
    IsLimit ((tensorLeft N).mapCone
      ((algebraSectionModulePresheaf f).mapCone (Pairwise.cocone U).op)) := by
  classical
  letI := Fintype.ofFinite ι
  exact isLimitOfPreserves (tensorLeft N) (algebraSectionPairwiseLimit f U)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSectionModules
