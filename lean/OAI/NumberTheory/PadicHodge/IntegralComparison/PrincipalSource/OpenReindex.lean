import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenRestriction

/-! # Open Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenReindex

noncomputable section

/-! The principal reindex from the actual appLE coefficient map is
exactly source-open restriction. Both its opens and additive section
maps retain the original ambient principal objects. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {Y Z : Scheme.{u}} (π : Y ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hVa : IsAffineOpen V)
  (hV : V ≤ π ⁻¹ᵁ U)

def scalar : Γ(Z,U) →+* Γ(Y,V) := (π.appLE U V hV).hom

def reindex : Principal.SectionPresheaf.Index U ⥤ Principal.SectionPresheaf.Index V := Principal.CoefficientChange.functor (scalar π U V hV)

instance reindex_preserves : PreservesFiniteLimits (reindex π U V hV) :=
  Principal.CoefficientProducts.preserves (scalar π U V hV)

theorem reindex_obj_val (r : Principal.SectionPresheaf.Index U) :
    ((reindex π U V hV).obj r).val = π.appLE U V hV r.val := rfl

def wideOpens : Principal.SectionPresheaf.Index U ⥤ Y.Opens := Principal.AdditiveSections.opens U hU ⋙ Opens.map π.base

def geometricOpens : Principal.SectionPresheaf.Index U ⥤ Y.Opens :=
  wideOpens π U hU ⋙ RelativeCech.Intersections.intersect V

def nativeOpens : Principal.SectionPresheaf.Index U ⥤ Y.Opens :=
  reindex π U V hV ⋙ Principal.AdditiveSections.opens V hVa

theorem open_eq (r : Principal.SectionPresheaf.Index U) :
    (nativeOpens π U V hVa hV).obj r = V ⊓ π ⁻¹ᵁ (Z.basicOpen r.val) :=
  Scheme.basicOpen_appLE π V U hV r.val

theorem opens_eq : nativeOpens π U V hVa hV = geometricOpens π U hU V :=
  CategoryTheory.Functor.ext (open_eq π U V hVa hV) (fun _ _ _ => Subsingleton.elim _ _)

def geometricInclusion : geometricOpens π U hU V ⟶ wideOpens π U hU where
  app _ := homOfLE inf_le_right

def nativeInclusion : nativeOpens π U V hVa hV ⟶ wideOpens π U hU where
  app r := homOfLE (by rw [open_eq]; exact inf_le_right)

private abbrev sectionPresheaf (N : Y.Modules) : Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N).obj

variable (N : Y.Modules)

def nativeSections : (Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (reindex π U V hV).op ⋙ (Principal.AdditiveSections.additiveFunctor V hVa).obj N

def geometricSections : (Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (geometricOpens π U hU V).op ⋙ sectionPresheaf N

def sectionsIso : nativeSections π U V hVa hV N ≅ geometricSections π U hU V N :=
  NatIso.ofComponents
    (fun r => (sectionPresheaf N).mapIso ((eqToIso (open_eq π U V hVa hV r.unop)).symm.op))
    (fun {_ _} a => by
      change (sectionPresheaf N).map _ ≫ (sectionPresheaf N).map _ =
        (sectionPresheaf N).map _ ≫ (sectionPresheaf N).map _
      rw [← (sectionPresheaf N).map_comp, ← (sectionPresheaf N).map_comp]
      congr 1)

def restriction : (wideOpens π U hU).op ⋙ sectionPresheaf N ⟶
    nativeSections π U V hVa hV N :=
  Functor.whiskerRight (NatTrans.op (nativeInclusion π U hU V hVa hV)) (sectionPresheaf N)

theorem restriction_app (r : Principal.SectionPresheaf.Index U) :
    (restriction π U hU V hVa hV N).app (op r) =
      N.presheaf.map (homOfLE ((nativeInclusion π U hU V hVa hV).app r).le).op := rfl

theorem restriction_square :
    restriction π U hU V hVa hV N ≫ (sectionsIso π U hU V hVa hV N).hom =
      Functor.whiskerRight (NatTrans.op (geometricInclusion π U hU V)) (sectionPresheaf N) := by
  apply NatTrans.ext
  funext r
  change (sectionPresheaf N).map _ ≫ (sectionPresheaf N).map _ = (sectionPresheaf N).map _
  rw [← (sectionPresheaf N).map_comp]
  congr 1

def pushforwardIso :
    (Principal.AdditiveSections.additiveFunctor U hU).obj ((Scheme.Modules.pushforward π).obj N) ≅
      (wideOpens π U hU).op ⋙ sectionPresheaf N :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {_ _} _ => rfl)

abbrev extensionOpen (r : Principal.SectionPresheaf.Index U) := V.ι ''ᵁ (V.ι ⁻¹ᵁ (π ⁻¹ᵁ (Z.basicOpen r.val)))

theorem extensionOpen_eq (r : Principal.SectionPresheaf.Index U) :
    extensionOpen π U V r = (geometricOpens π U hU V).obj r := by
  rw [extensionOpen, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  rfl

def extensionOpens : Principal.SectionPresheaf.Index U ⥤ Y.Opens :=
  wideOpens π U hU ⋙ Opens.map V.ι.base ⋙ V.ι.opensFunctor

def extensionSections : (Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (extensionOpens π U hU V).op ⋙ sectionPresheaf N

def extensionCoordinates :
    (Principal.AdditiveSections.additiveFunctor U hU).obj
        ((Scheme.Modules.pushforward π).obj (OpenRestriction.extension V N)) ≅
      extensionSections π U hU V N :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {_ _} _ => rfl)

def extensionGeometricIso : extensionSections π U hU V N ≅ geometricSections π U hU V N :=
  NatIso.ofComponents
    (fun r => (sectionPresheaf N).mapIso ((eqToIso (extensionOpen_eq π U hU V r.unop)).symm.op))
    (fun {_ _} a => by
      change (sectionPresheaf N).map _ ≫ (sectionPresheaf N).map _ =
        (sectionPresheaf N).map _ ≫ (sectionPresheaf N).map _
      rw [← (sectionPresheaf N).map_comp, ← (sectionPresheaf N).map_comp]
      congr 1)

def extensionIso :
    (Principal.AdditiveSections.additiveFunctor U hU).obj
        ((Scheme.Modules.pushforward π).obj (OpenRestriction.extension V N)) ≅
      geometricSections π U hU V N :=
  extensionCoordinates π U hU V N ≪≫ extensionGeometricIso π U hU V N

def extensionInclusion : extensionOpens π U hU V ⟶ wideOpens π U hU where
  app r := homOfLE (V.ι.image_preimage_le (π ⁻¹ᵁ (Z.basicOpen r.val)))

def extensionRestriction : (wideOpens π U hU).op ⋙ sectionPresheaf N ⟶
    extensionSections π U hU V N :=
  Functor.whiskerRight (NatTrans.op (extensionInclusion π U hU V)) (sectionPresheaf N)

theorem actual_restriction_coordinates :
    (Principal.AdditiveSections.additiveFunctor U hU).map
        ((Scheme.Modules.pushforward π).map ((Scheme.Modules.restrictAdjunction V.ι).unit.app N)) ≫
      (extensionCoordinates π U hU V N).hom =
    (pushforwardIso π U hU N).hom ≫ extensionRestriction π U hU V N := by
  apply NatTrans.ext
  funext r
  rfl

theorem extension_restriction_square :
    extensionRestriction π U hU V N ≫ (extensionGeometricIso π U hU V N).hom =
      Functor.whiskerRight (NatTrans.op (geometricInclusion π U hU V)) (sectionPresheaf N) := by
  apply NatTrans.ext
  funext r
  change (sectionPresheaf N).map _ ≫ (sectionPresheaf N).map _ = (sectionPresheaf N).map _
  rw [← (sectionPresheaf N).map_comp]
  congr 1

theorem actual_restriction :
    (Principal.AdditiveSections.additiveFunctor U hU).map
        ((Scheme.Modules.pushforward π).map ((Scheme.Modules.restrictAdjunction V.ι).unit.app N)) ≫
      (extensionIso π U hU V N).hom =
    (pushforwardIso π U hU N).hom ≫ restriction π U hU V hVa hV N ≫
      (sectionsIso π U hU V hVa hV N).hom := by
  change _ ≫ ((extensionCoordinates π U hU V N).hom ≫
    (extensionGeometricIso π U hU V N).hom) = _
  rw [← Category.assoc, actual_restriction_coordinates, Category.assoc,
    extension_restriction_square, restriction_square]

def extensionToNative :
    (Principal.AdditiveSections.additiveFunctor U hU).obj
        ((Scheme.Modules.pushforward π).obj (OpenRestriction.extension V N)) ≅
      nativeSections π U V hVa hV N :=
  extensionIso π U hU V N ≪≫ (sectionsIso π U hU V hVa hV N).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenReindex
