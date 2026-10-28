import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiber

/-! # Affine Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.AffineMap.BundleCycles

noncomputable section

/-!
# LineBundleCycles: maps between affine schemes glued over a common base

A natural transformation of the actual affine algebras induces a morphism
of the glued schemes. Compatibility with constants proves that this is a
morphism over the base and that its restrictions are pullback charts.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} {F G : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat}
variable {α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F}
variable {β : (toOpensFunctor X).op ⋙ X.presheaf ⟶ G}
variable (hα : α.Coequifibered) (hβ : β.Coequifibered)

instance relativeAffineGlueData_isLocallyDirected :
    ((relativeGluingData hα).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- Compatible affine spectrum maps into the gluing of the target charts. -/
def relativeAffineMapCocone (η : F ⟶ G) : Cocone (relativeGluingData hβ).functor where
  pt := (relativeGluingData hα).glued
  ι := Functor.whiskerRight η.rightOp Scheme.Spec ≫
    (colimit.cocone (relativeGluingData hα).functor).ι

/-- The morphism induced by a natural transformation of the affine algebras. -/
def relativeAffineMap (η : F ⟶ G) :
    (relativeGluingData hβ).glued ⟶ (relativeGluingData hα).glued :=
  colimit.desc _ (relativeAffineMapCocone hα hβ η)

theorem relativeAffineMap_on_chart (η : F ⟶ G) (U : X.AffineZariskiSite) :
    (relativeGluingData hβ).cover.f U ≫ relativeAffineMap hα hβ η =
      Spec.map (η.app (.op U)) ≫ (relativeGluingData hα).cover.f U :=
  colimit.ι_desc (relativeAffineMapCocone hα hβ η) U

variable (η : F ⟶ G) (hη : α ≫ η = β)
include hη

theorem relativeAffineMap_chart_toBase (U : X.AffineZariskiSite) :
    Spec.map (η.app (.op U)) ≫ (relativeGluingData hα).natTrans.app U =
      (relativeGluingData hβ).natTrans.app U := by
  change Spec.map (η.app (.op U)) ≫
      (Spec.map (α.app (.op U)) ≫ (restrictIsoSpec X).inv.app U) =
    Spec.map (β.app (.op U)) ≫ (restrictIsoSpec X).inv.app U
  rw [← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun a => Spec.map a ≫ (restrictIsoSpec X).inv.app U)
    (congrArg (fun γ => γ.app (.op U)) hη)

/-- The map of gluings respects the specified structure maps to the common base. -/
theorem relativeAffineMap_toBase :
    relativeAffineMap hα hβ η ≫ (relativeGluingData hα).toBase =
      (relativeGluingData hβ).toBase := by
  apply (relativeGluingData hβ).cover.hom_ext
  intro U
  let q : (relativeGluingData hβ).cover.X U ⟶ (relativeGluingData hα).cover.X U :=
    Spec.map (η.app (.op U))
  have hd := (relativeGluingData hα).ι_toBase U
  have hs := (relativeGluingData hβ).ι_toBase U
  have hq : q ≫ (relativeGluingData hα).natTrans.app U =
      (relativeGluingData hβ).natTrans.app U := relativeAffineMap_chart_toBase hα hβ η hη U
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (relativeGluingData hα).toBase)
      (relativeAffineMap_on_chart hα hβ η U)).trans
    ((Category.assoc q _ _).trans
    ((congrArg (fun k => q ≫ k) hd).trans
    ((Category.assoc q _ _).symm.trans
    ((congrArg (fun k => k ≫ (directedCover X).f U) hq).trans hs.symm)))))

/-- Each affine map is precisely the pullback of the global morphism to that target chart. -/
theorem relativeAffineMap_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback (Spec.map (η.app (.op U))) ((relativeGluingData hβ).cover.f U)
      ((relativeGluingData hα).cover.f U) (relativeAffineMap hα hβ η) := by
  have h := (relativeGluingData hβ).isPullback_natTrans_ι_toBase U
  rw [← relativeAffineMap_chart_toBase hα hβ η hη U,
    ← relativeAffineMap_toBase hα hβ η hη] at h
  exact h.of_right (relativeAffineMap_on_chart hα hβ η U).symm
    ((relativeGluingData hα).isPullback_natTrans_ι_toBase U)

/-- Surjective affine algebra maps glue to a closed immersion. -/
theorem relativeAffineMap_isClosedImmersion
    (hsurj : ∀ U : X.AffineZariskiSite, Function.Surjective (η.app (.op U))) :
    IsClosedImmersion (relativeAffineMap hα hβ η) := by
  apply Global.SpecialFiber.BundleCycles.isClosedImmersion_of_cover_pullbacks (relativeAffineMap hα hβ η)
    (relativeGluingData hα).cover (relativeGluingData hβ).cover.X
    (relativeGluingData hβ).cover.f (fun U => Spec.map (η.app (.op U)))
    (relativeAffineMap_chart_isPullback hα hβ η hη)
  intro U
  exact IsClosedImmersion.spec_of_surjective _ (hsurj U)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.AffineMap.BundleCycles
