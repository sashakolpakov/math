import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! # Presheaf Localization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafLocalization.PresheafLocalizationTransport

noncomputable section

/-! Localization of a module-valued presheaf map is invariant under a natural isomorphism. -/

open _root_.CategoryTheory

universe u v w

variable {R : Type u} [CommRing R] {C : Type v} [Category.{w} C]
  {P Q : C ⥤ ModuleCat.{u} R} (e : P ≅ Q) {U V : C} (f : U ⟶ V) (S : Submonoid R)

include e in
theorem isLocalized [IsLocalizedModule S (Q.map f).hom] : IsLocalizedModule S (P.map f).hom := by
  have h : (e.hom.app V).hom.comp (P.map f).hom = (Q.map f).hom.comp (e.hom.app U).hom :=
    congrArg ModuleCat.Hom.hom (e.hom.naturality f)
  apply (IsLocalizedModule.comp_iff_of_bijective_left S (e.hom.app V).hom
    (ConcreteCategory.bijective_of_isIso (e.hom.app V))).mp
  rw [h]
  exact (IsLocalizedModule.comp_iff_of_bijective_right S (e.hom.app U).hom
    (ConcreteCategory.bijective_of_isIso (e.hom.app U))).mpr inferInstance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafLocalization.PresheafLocalizationTransport
