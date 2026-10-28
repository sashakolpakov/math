import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.AffineSectionsFlat
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Base Line Bundle Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BaseLineBundleSections

noncomputable section

/-! Line-bundle sections on an affine open are flat for the actual scalar action of a flat morphism to an affine base. -/
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)

def baseSectionScalarMap (U : X.Opens) : Γ(S, ⊤) →+* Γ(X, U) :=
  (f.appTop ≫ X.presheaf.map U.leTop.op).hom

theorem baseSectionScalarMap_eq (U : X.Opens) :
    baseSectionScalarMap f U = (f.appLE ⊤ U (by simp)).hom := by
  rfl

theorem flat_base_lineBundle_sections [IsAffine S] [Flat f] (L : Line.Bundles.LineBundle X)
    (U : X.affineOpens) : Module.Flat Γ(S, ⊤) ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf).obj (op U.1)) := by
  let : Algebra Γ(S, ⊤) Γ(X, U.1) := (baseSectionScalarMap f U.1).toAlgebra
  have hf : (baseSectionScalarMap f U.1).Flat := by
    rw [baseSectionScalarMap_eq]
    exact f.flat_appLE (isAffineOpen_top S) U.2 _
  have : Module.Flat Γ(S, ⊤) Γ(X, U.1) := hf
  let : Module Γ(X, U.1) ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf).obj (op U.1)) :=
    inferInstanceAs (Module Γ(X, U.1) Γ(L.sheaf, U.1))
  have : IsScalarTower Γ(S, ⊤) Γ(X, U.1) ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf).obj (op U.1)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have : Module.Flat Γ(X, U.1) ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf).obj (op U.1)) :=
    LineBundle.AffineSectionsFlat.lineBundle_affineOpen_sections_flat L U
  exact Module.Flat.trans Γ(S, ⊤) Γ(X, U.1) ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf).obj (op U.1))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BaseLineBundleSections
