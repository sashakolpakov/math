import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureSectionClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleMapCoordinates

/-! # Single Presheaf Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.SinglePresheafCoordinates

noncomputable section

/-! The original module-single and sheaf-single coordinate maps
factor the literal presheaf single comparison on every principal chart. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {X : Scheme.{u}} (N : X.Modules) (c : ℕ)

abbrev presheaf := (Relative.AdditiveCechConcentration.presheaves (X := X)).obj N
abbrev moduleSingle := (single X.Modules (.up ℕ) c).obj N

def lastIso : Global.PureSectionClass.sheafCoefficients N c ≅
    (single (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) c).obj (presheaf N) :=
  (singleMapHomologicalComplex
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (.up ℕ) c).app
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)

def iso : Relative.AdditiveCechConcentration.coefficients (moduleSingle N c) ≅
    (single (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) c).obj (presheaf N) :=
  Principal.RelativeSupportedClass.singleCoefficientIso N c ≪≫ lastIso N c

theorem self : (iso N c).hom.f c ≫ (singleObjXSelf (.up ℕ) c (presheaf N)).hom =
    (Relative.AdditiveCechConcentration.presheaves (X := X)).map
      (singleObjXSelf (.up ℕ) c N).hom := by
  let H := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let G := SheafOfModules.toSheaf X.ringCatSheaf
  change (H.map (((singleMapHomologicalComplex G (.up ℕ) c).hom.app N).f c) ≫
    ((singleMapHomologicalComplex H (.up ℕ) c).hom.app (G.obj N)).f c) ≫
      (singleObjXSelf (.up ℕ) c (H.obj (G.obj N))).hom =
    H.map (G.map (singleObjXSelf (.up ℕ) c N).hom)
  rw [singleMapHomologicalComplex_hom_app_self, singleMapHomologicalComplex_hom_app_self]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]

variable {D : Type v} [Category.{w} D] [Abelian D] [HasCoproducts.{0} D]
  (F : (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ CochainComplex D ℕ) [F.Additive]

def bicomplexIso := (F.mapHomologicalComplex (.up ℕ)).mapIso (iso N c)

theorem coordinates (g : ℕ) :
    homologyMap (HomologicalComplex₂.total.mapIso (bicomplexIso N c F) (.up ℕ)).hom (g+c) ≫
      (IntegralComparison.Functor.SingleTotal.homologyIso F (presheaf N) c g).hom =
    (IntegralComparison.Functor.SingleTotal.homologyIso
      (Relative.AdditiveCechConcentration.presheaves (X := X) ⋙ F) N c g).hom := by
  apply (IntegralComparison.Functor.SingleMapCoordinates.comparison
    (Relative.AdditiveCechConcentration.presheaves (X := X) ⋙ F) F N (presheaf N) c
    (bicomplexIso N c F).hom (𝟙 _) ?_ g).trans
  · simp only [homologyMap_id, Category.comp_id]
  · change F.map ((iso N c).hom.f c) ≫ F.map (singleObjXSelf (.up ℕ) c (presheaf N)).hom =
      F.map ((Relative.AdditiveCechConcentration.presheaves (X := X)).map
        (singleObjXSelf (.up ℕ) c N).hom) ≫ 𝟙 _
    rw [← F.map_comp, self, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.SinglePresheafCoordinates
