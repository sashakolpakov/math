import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraPresheafScalars
import OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Algebra Sheaf Scalars -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars

noncomputable section

/-!
# IntegralComparison: the original structure-sheaf modules retain their native base-ring sheaves
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [CommRing k] (X : Over (Spec (CommRingCat.of k)))

abbrev presheaves := AlgebraPresheafScalars.functor k (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X)

def obj (M : X.left.Modules) : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} k) :=
  ⟨(presheaves k X).obj M.val, Presheaf.isSheaf_of_isSheaf_comp _ _
    (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}) M.isSheaf⟩

def functor : X.left.Modules ⥤ Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} k) where
  obj := AlgebraSheafScalars.obj k X
  map φ := ⟨(presheaves k X).map φ.val⟩

instance additive : (functor k X).Additive where
  map_add := rfl

def underlyingIso : functor k X ⋙
    sheafCompose (Opens.grothendieckTopology X.left) (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}) ≅
      SheafOfModules.toSheaf.{u} X.left.ringCatSheaf := Iso.refl _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars
