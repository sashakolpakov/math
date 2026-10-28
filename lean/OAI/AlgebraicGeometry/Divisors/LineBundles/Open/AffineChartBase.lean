import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Deformation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.GlobalIdealPullback

/-! # Affine Chart Base -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.AffineChartBase.BundleCycles

noncomputable section

section

/-! An actual open immersion maps affine Zariski charts and their principal-open restrictions to their affine images. The section isomorphisms identify the pulled-back center ideals exactly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i]

def openAffineSiteImage (U : X.AffineZariskiSite) : Y.AffineZariskiSite :=
  ⟨i ''ᵁ U.1, U.2.image_of_isOpenImmersion i⟩

theorem openAffineSiteImage_mono : Monotone (openAffineSiteImage i) := by
  intro U V h
  obtain ⟨s, hs⟩ := h
  refine ⟨(i.appIso V.1).inv s, ?_⟩
  exact (Scheme.image_basicOpen i s).symm.trans (congrArg (fun U => i ''ᵁ U) hs)

def openAffineSiteImageFunctor : X.AffineZariskiSite ⥤ Y.AffineZariskiSite :=
  (openAffineSiteImage_mono i).functor

theorem openAffineSiteImage_ideal (I : Y.IdealSheafData) (U : X.AffineZariskiSite) :
    (I.comap i).ideal U = (I.ideal (openAffineSiteImage i U)).map (i.appIso U.1).hom.hom := by
  exact (Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I i ⟨U.1, U.2⟩).trans
    (GlobalIdealPullback.BundleCycles.commRingIso_comap_inv (i.appIso U.1) _)

theorem openAffineSiteImage_sections_naturality {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    Y.presheaf.map (homOfLE (i.image_mono (toOpens_mono h.le))).op ≫ (i.appIso U.1).hom =
      (i.appIso V.1).hom ≫ X.presheaf.map (homOfLE (toOpens_mono h.le)).op := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

end

/-! The actual spectrum map of the section isomorphism identifies an affine open with its image over the original scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] (U : X.AffineZariskiSite)

theorem openAffineSiteImage_fromSpec :
    Spec.map (i.appIso U.1).hom ≫ (openAffineSiteImage i U).2.fromSpec = U.2.fromSpec ≫ i := by
  rw [Scheme.Hom.appIso_hom']
  exact IsAffineOpen.SpecMap_appLE_fromSpec i (openAffineSiteImage i U).2 U.2 (i.preimage_image_eq U.1).ge

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.AffineChartBase.BundleCycles
