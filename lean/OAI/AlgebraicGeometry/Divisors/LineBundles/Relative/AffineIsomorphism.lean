import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.AffineMap
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Affine Isomorphism -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.AffineIsomorphism.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual affine algebra isomorphisms glue to a scheme isomorphism -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u

theorem isIso_of_cover_pullbacks {A B : Scheme.{u}} (f : A ⟶ B)
    (C : B.OpenCover) (Z : C.I₀ → Scheme.{u}) (a : ∀ i, Z i ⟶ A) (b : ∀ i, Z i ⟶ C.X i)
    (h : ∀ i, IsPullback (b i) (a i) (C.f i) f) (hb : ∀ i, IsIso (b i)) : IsIso f := by
  apply IsZariskiLocalAtTarget.of_openCover (P := CategoryTheory.MorphismProperty.isomorphisms Scheme) C
  intro i
  let hi := (h i).flip
  let := hb i
  have hc : IsIso (hi.isoPullback.inv ≫ b i) := inferInstance
  exact (congrArg (fun k => IsIso k) hi.isoPullback_inv_snd).mp hc

variable {X : Scheme.{u}} {F G : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat}
    {α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F}
    {β : (toOpensFunctor X).op ⋙ X.presheaf ⟶ G}
    (hα : α.Coequifibered) (hβ : β.Coequifibered) (η : F ⟶ G) (hη : α ≫ η = β)

include hη in
theorem relativeAffineMap_isIso (hbij : ∀ U : X.AffineZariskiSite, Function.Bijective (η.app (.op U))) :
    IsIso (AffineMap.BundleCycles.relativeAffineMap hα hβ η) := by
  apply isIso_of_cover_pullbacks (AffineMap.BundleCycles.relativeAffineMap hα hβ η)
    (relativeGluingData hα).cover (relativeGluingData hβ).cover.X
    (relativeGluingData hβ).cover.f (fun U => Spec.map (η.app (.op U)))
    (AffineMap.BundleCycles.relativeAffineMap_chart_isPullback hα hβ η hη)
  intro U
  exact isIso_SpecMap_iff.mpr (hbij U)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.AffineIsomorphism.BundleCycles
