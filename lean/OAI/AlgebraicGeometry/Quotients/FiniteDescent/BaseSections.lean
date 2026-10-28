import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvertibleSections
import OAI.AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Base Sections -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseSections

noncomputable section

/-! Flat affine sections with their scalar action from a flat base morphism. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.BaseSectionsFlat

variable {X S : Scheme.{u}} (f : X ⟶ S)

def scalarMap (U : X.Opens) : Γ(S, ⊤) →+* Γ(X, U) :=
  (f.appTop ≫ X.presheaf.map U.leTop.op).hom

theorem scalarMap_eq (U : X.Opens) :
    scalarMap f U = (f.appLE ⊤ U (by simp)).hom := by
  change (f.appTop ≫ X.presheaf.map U.leTop.op).hom = _
  rw [Scheme.Hom.appTop, Scheme.Hom.appLE]
  rfl

theorem flat [IsAffine S] [Flat f] (M : X.Modules) (hM : SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible M)
    (U : X.affineOpens) : Module.Flat Γ(S, ⊤) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).obj (op U.1)) := by
  let : Algebra Γ(S, ⊤) Γ(X, U.1) := (scalarMap f U.1).toAlgebra
  have hf : (scalarMap f U.1).Flat := by
    rw [scalarMap_eq]
    exact f.flat_appLE (isAffineOpen_top S) U.2 _
  have : Module.Flat Γ(S, ⊤) Γ(X, U.1) := hf
  let : Module Γ(X, U.1) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).obj (op U.1)) :=
    inferInstanceAs (Module Γ(X, U.1) Γ(M, U.1))
  have : IsScalarTower Γ(S, ⊤) Γ(X, U.1) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).obj (op U.1)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have : Module.Flat Γ(X, U.1) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).obj (op U.1)) :=
    InvertibleSections.Construction.InvertibleSectionsFlat.flat M hM U
  exact Module.Flat.trans Γ(S, ⊤) Γ(X, U.1) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).obj (op U.1))

end Construction.BaseSectionsFlat

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseSections
