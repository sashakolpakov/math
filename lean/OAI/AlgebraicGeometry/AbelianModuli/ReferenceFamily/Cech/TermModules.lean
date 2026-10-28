import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.TermRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.Algebra.Module.TransferInstance

/-! # Term Modules -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.TermModules

noncomputable section

/-! The original sheaf-level Cech terms of regular functions retain
their actual module structure over the algebraic structure sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open _root_.TopCat.Sheaf

def structureAbelianSheaf (X : Scheme.{0}) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj (HilbertConstruction.Line.Bundles.structureModule X)

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens) (n : ℕ)

local instance restrictedRegularModule (V A : X.Opens) :
    Module Γ(X, V) ((structureAbelianSheaf X).obj.obj (op (V ⊓ A))) :=
  Module.compHom Γ(X, V ⊓ A) (X.presheaf.map (homOfLE (show V ⊓ A ≤ V from inf_le_left)).op).hom

instance cechTermSectionModule (V : X.Opens) :
    Module Γ(X, V) ((SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm (structureAbelianSheaf X) U n).obj.obj (op V)) :=
  (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (structureAbelianSheaf X) U n V).module Γ(X, V)

theorem cechTermCoordinates_smul (V : X.Opens) (a : Γ(X, V))
    (c : (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm (structureAbelianSheaf X) U n).obj.obj (op V)) (i : Fin (n + 1) → I) :
    SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (structureAbelianSheaf X) U n V (a • c) i =
      X.presheaf.map (homOfLE (show V ⊓ (∏ᶜ fun k : Fin (n + 1) => U (i k)) ≤ V from inf_le_left)).op a *
        (show Γ(X, V ⊓ (∏ᶜ fun k : Fin (n + 1) => U (i k))) from
          SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (structureAbelianSheaf X) U n V c i) := by
  exact congrArg (fun q => q i)
    ((SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (structureAbelianSheaf X) U n V).apply_symm_apply (a •
      SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (structureAbelianSheaf X) U n V c))

theorem cechTerm_map_smul {V W : X.Opens} (h : W ≤ V) (a : Γ(X, V))
    (c : (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm (structureAbelianSheaf X) U n).obj.obj (op V)) :
    (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm (structureAbelianSheaf X) U n).obj.map (homOfLE h).op (a • c) =
      X.presheaf.map (homOfLE h).op a • (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm (structureAbelianSheaf X) U n).obj.map (homOfLE h).op c := by
  apply (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (structureAbelianSheaf X) U n W).injective
  funext i
  rw [TermRestriction.cechTermCoordinates_restrict, cechTermCoordinates_smul, cechTermCoordinates_smul,
    TermRestriction.cechTermCoordinates_restrict]
  let A := ∏ᶜ fun k : Fin (n + 1) => U (i k)
  change X.presheaf.map (homOfLE (inf_le_inf_right A h)).op
      (X.presheaf.map (homOfLE (show V ⊓ A ≤ V from inf_le_left)).op a * _) =
    X.presheaf.map (homOfLE (show W ⊓ A ≤ W from inf_le_left)).op (X.presheaf.map (homOfLE h).op a) * _
  rw [map_mul]
  congr 1
  exact ConcreteCategory.congr_hom
    ((X.presheaf.map_comp _ _).symm.trans
      ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _))) a

local instance cechTermRingSectionModule (V : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj V) ((SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm (structureAbelianSheaf X) U n).obj.obj V) :=
  cechTermSectionModule X U n V.unop

def cechTermModule : X.Modules where
  val := PresheafOfModules.ofPresheaf (R := X.ringCatSheaf.obj)
    (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm (structureAbelianSheaf X) U n).obj
      (fun {_ _} f a c => cechTerm_map_smul X U n (leOfHom f.unop) a c)
  isSheaf := (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm (structureAbelianSheaf X) U n).property

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.TermModules
