import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Category.Preorder

/-! # Presheaf Restriction Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafRestrictionTransport

noncomputable section

/-! Identifying equal opens commutes with actual presheaf restriction. -/

open _root_.CategoryTheory Opposite

universe u v

variable {C : Type v} [Preorder C] {R : Type u} [CommRing R]

theorem modulePresheaf_restriction_transport (F : Cᵒᵖ ⥤ ModuleCat.{u} R)
    {U V U' V' : C} (hU : U = U') (hV : V = V') (h : V ≤ U) (h' : V' ≤ U') :
    F.map (homOfLE h).op ≫ (F.mapIso (eqToIso hV.symm).op).hom =
      (F.mapIso (eqToIso hU.symm).op).hom ≫ F.map (homOfLE h').op := by
  simp only [Functor.mapIso_hom, ← F.map_comp]
  exact congrArg F.map (Subsingleton.elim _ _)

theorem modulePresheaf_restriction_transport_apply (F : Cᵒᵖ ⥤ ModuleCat.{u} R)
    {U V U' V' : C} (hU : U = U') (hV : V = V') (h : V ≤ U) (h' : V' ≤ U')
    (x : F.obj (op U)) :
    (F.mapIso (eqToIso hV.symm).op).hom (F.map (homOfLE h).op x) =
      F.map (homOfLE h').op ((F.mapIso (eqToIso hU.symm).op).hom x) :=
  ConcreteCategory.congr_hom (modulePresheaf_restriction_transport F hU hV h h') x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafRestrictionTransport
