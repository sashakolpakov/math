import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationRestriction
import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Presentation Sheaf Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationSheafRestriction

noncomputable section

/-! Canonical sheafification compatibility transports maps of the original presentation resolutions. -/

open _root_.CategoryTheory

universe u v w v' w'

variable (R : Type u) [CommRing R] {C : Type v} [Category.{w} C]
  {D : Type v'} [Category.{w'} D] (G : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J (ModuleCat.{u} R)] [HasSheafify K (ModuleCat.{u} R)]
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ (F : Cᵒᵖ ⥤ ModuleCat.{u} R), G.op.HasPointwiseRightKanExtension F]

def restriction : Sheaf K (ModuleCat.{u} R) ⥤ Sheaf J (ModuleCat.{u} R) :=
  G.sheafPushforwardContinuous (ModuleCat.{u} R) J K

instance restriction_additive : (restriction R G J K).Additive where
  map_add := by intros; rfl

def compatibility : PresentationRestriction.restriction R G ⋙ presheafToSheaf J (ModuleCat.{u} R) ≅
    presheafToSheaf K (ModuleCat.{u} R) ⋙ restriction R G J K :=
  G.pushforwardContinuousSheafificationCompatibility (ModuleCat.{u} R) J K

def constantIso : (restriction R G J K).obj ((constantSheaf K (ModuleCat.{u} R)).obj (ModuleCat.of R R)) ≅
    (constantSheaf J (ModuleCat.{u} R)).obj (ModuleCat.of R R) :=
  (compatibility R G J K).symm.app (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.coefficientPresheaf (C := D) R)

variable {F : Cᵒᵖ ⥤ Type u} {H : Dᵒᵖ ⥤ Type u} (a : F ⟶ G.op ⋙ H)

def map : AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.sheafComplex R F J ⟶
    ((restriction R G J K).mapHomologicalComplex (.down ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.sheafComplex R H K) :=
  ((presheafToSheaf J (ModuleCat.{u} R)).mapHomologicalComplex (.down ℕ)).map
    (PresentationRestriction.map R G a) ≫
      (NatIso.mapHomologicalComplex (compatibility R G J K) (.down ℕ)).hom.app
        (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R H)

theorem component (n : ℕ) : (PresentationSheafRestriction.map R G J K a).f n =
    (presheafToSheaf J (ModuleCat.{u} R)).map ((PresentationRestriction.map R G a).f n) ≫
      (compatibility R G J K).hom.app ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R H).X n) := rfl

instance map_isIso [IsIso a] : IsIso (PresentationSheafRestriction.map R G J K a) := by
  let h : IsIso (PresentationRestriction.map R G a) := PresentationRestriction.map_isIso R G a
  let S := (presheafToSheaf J (ModuleCat.{u} R)).mapHomologicalComplex (.down ℕ)
  let hs : IsIso (S.map (PresentationRestriction.map R G a)) := by infer_instance
  let e := NatIso.mapHomologicalComplex (compatibility R G J K) (.down ℕ)
  exact ((asIso (S.map (PresentationRestriction.map R G a))) ≪≫
    e.app (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R H)).isIso_hom

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationSheafRestriction
