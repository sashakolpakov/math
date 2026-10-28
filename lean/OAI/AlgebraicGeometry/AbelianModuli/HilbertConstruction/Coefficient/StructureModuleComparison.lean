import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheafFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSectionModules

/-! # Structure Module Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.StructureModuleComparison

noncomputable section

/-! Coefficient sections of the structure module agree with the underlying modules of the coefficient-algebra presheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R] (f : R →+* Γ(X, ⊤))

def coefficientStructureModuleComponent (U : X.Opens) :
    (ModulePresheaf.coefficientModulePresheaf f (Line.Bundles.structureModule X)).obj (.op U) ≃ₗ[R]
      (AlgebraSectionModules.algebraSectionModulePresheaf f).obj (.op U) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coefficientStructureModuleIso :
    ModulePresheaf.coefficientModulePresheaf f (Line.Bundles.structureModule X) ≅ AlgebraSectionModules.algebraSectionModulePresheaf f :=
  NatIso.ofComponents (fun U => (coefficientStructureModuleComponent f U.unop).toModuleIso) (by
    intro U V h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.StructureModuleComparison
