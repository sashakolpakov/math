import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.SchemeImage
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.ClosedImageRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.Open.InverseRestriction

/-! # Strict Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Integral.StrictTransform.Construction

noncomputable section

/-! Integral strict transforms formed as actual scheme-theoretic images over a protected open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

instance schemeOpen_noetherianSpace {X : Scheme.{u}} [NoetherianSpace X] (U : X.Opens) :
    NoetherianSpace U.toScheme :=
  U.ι.isOpenEmbedding.isInducing.noetherianSpace

def strictTransformOpenMap {Y X : Scheme.{u}} (π : Y ⟶ X)
    (H : X.IdealSheafData) (U : X.Opens) [IsIso (π ∣_ U)] :
    (H.subschemeι ⁻¹ᵁ U).toScheme ⟶ Y :=
  ((H.subschemeι ∣_ U) ≫ inv (π ∣_ U)) ≫ (π ⁻¹ᵁ U).ι

theorem strictTransformOpenMap_over {Y X : Scheme.{u}} (π : Y ⟶ X)
    (H : X.IdealSheafData) (U : X.Opens) [IsIso (π ∣_ U)] :
    strictTransformOpenMap π H U ≫ π = (H.subschemeι ⁻¹ᵁ U).ι ≫ H.subschemeι := by
  simp only [strictTransformOpenMap, Category.assoc, ← morphismRestrict_ι,
    IsIso.inv_hom_id_assoc]

instance strictTransformOpenMap_isImmersion {Y X : Scheme.{u}} (π : Y ⟶ X)
    (H : X.IdealSheafData) (U : X.Opens) [IsIso (π ∣_ U)] :
    IsImmersion (strictTransformOpenMap π H U) := by
  unfold strictTransformOpenMap
  infer_instance

abbrev strictTransformIdeal {Y X : Scheme.{u}} (π : Y ⟶ X)
    (H : X.IdealSheafData) (U : X.Opens) [IsIso (π ∣_ U)] : Y.IdealSheafData :=
  (strictTransformOpenMap π H U).ker

theorem strictTransformIdeal_total_le {Y X : Scheme.{u}} (π : Y ⟶ X)
    (H : X.IdealSheafData) (U : X.Opens) [IsIso (π ∣_ U)] :
    H.comap π ≤ strictTransformIdeal π H U := by
  apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
  rw [strictTransformIdeal, Scheme.IdealSheafData.map_ker, strictTransformOpenMap_over]
  simpa only [H.ker_subschemeι] using
    (Scheme.Hom.le_ker_comp (H.subschemeι ⁻¹ᵁ U).ι H.subschemeι)

theorem strictTransformIdeal_isIntegral {Y X : Scheme.{u}} (π : Y ⟶ X)
    (H : X.IdealSheafData) (U : X.Opens) [IsIso (π ∣_ U)]
    [NoetherianSpace H.subscheme] [IsIntegral H.subscheme]
    [Nonempty (H.subschemeι ⁻¹ᵁ U).toScheme] :
    IsIntegral (strictTransformIdeal π H U).subscheme := by
  let : IsIntegral (H.subschemeι ⁻¹ᵁ U).toScheme :=
    isIntegral_of_isOpenImmersion (H.subschemeι ⁻¹ᵁ U).ι
  exact SchemeImage.Construction.scheme_image_isIntegral (strictTransformOpenMap π H U)

def strictTransformToBase {Y X : Scheme.{u}} (π : Y ⟶ X)
    (H : X.IdealSheafData) (U : X.Opens) [IsIso (π ∣_ U)] :
    (strictTransformIdeal π H U).subscheme ⟶ H.subscheme :=
  ClosedTransformMap.Construction.closedTransformMap π H (strictTransformIdeal π H U) (strictTransformIdeal_total_le π H U)

theorem strictTransformToBase_over {Y X : Scheme.{u}} (π : Y ⟶ X)
    (H : X.IdealSheafData) (U : X.Opens) [IsIso (π ∣_ U)] :
    strictTransformToBase π H U ≫ H.subschemeι =
      (strictTransformIdeal π H U).subschemeι ≫ π :=
  ClosedTransformMap.Construction.closedTransformMap_over π H _ _

theorem strictTransformToBase_isProper {Y X : Scheme.{u}} (π : Y ⟶ X) [IsProper π]
    (H : X.IdealSheafData) (U : X.Opens) [IsIso (π ∣_ U)] :
    IsProper (strictTransformToBase π H U) :=
  ClosedTransformMap.Construction.closedTransformMap_isProper π H _ _

theorem strictTransformOpenMap_toImage_over {Y X : Scheme.{u}} (π : Y ⟶ X)
    (H : X.IdealSheafData) (U : X.Opens) [IsIso (π ∣_ U)] :
    (strictTransformOpenMap π H U).toImage ≫ strictTransformToBase π H U =
      (H.subschemeι ⁻¹ᵁ U).ι := by
  apply (cancel_mono H.subschemeι).mp
  rw [Category.assoc, strictTransformToBase_over, ← Category.assoc]
  change ((strictTransformOpenMap π H U).toImage ≫
    (strictTransformOpenMap π H U).imageι) ≫ π = _
  rw [Scheme.Hom.toImage_imageι, strictTransformOpenMap_over]

theorem strictTransformOpenMap_toImage_opensRange {Y X : Scheme.{u}} (π : Y ⟶ X)
    (H : X.IdealSheafData) (U : X.Opens) [IsIso (π ∣_ U)]
    [NoetherianSpace H.subscheme] :
    (strictTransformOpenMap π H U).toImage.opensRange =
      strictTransformToBase π H U ⁻¹ᵁ (H.subschemeι ⁻¹ᵁ U) := by
  have he := Locally.ClosedImageRestriction.Construction.closed_open_image_opensRange
    ((H.subschemeι ∣_ U) ≫ inv (π ∣_ U)) (π ⁻¹ᵁ U).ι
  rw [Scheme.Opens.opensRange_ι] at he
  change (strictTransformOpenMap π H U).toImage.opensRange =
    (strictTransformIdeal π H U).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ U) at he
  rw [he]
  change ((strictTransformIdeal π H U).subschemeι ≫ π) ⁻¹ᵁ U =
    (strictTransformToBase π H U ≫ H.subschemeι) ⁻¹ᵁ U
  rw [strictTransformToBase_over]

theorem strictTransformToBase_restrict_isIso {Y X : Scheme.{u}} (π : Y ⟶ X)
    (H : X.IdealSheafData) (U : X.Opens) [IsIso (π ∣_ U)]
    [NoetherianSpace H.subscheme] :
    IsIso (strictTransformToBase π H U ∣_ (H.subschemeι ⁻¹ᵁ U)) :=
  Open.InverseRestriction.Construction.isIso_restrict_of_open_inverse _ _ (strictTransformOpenMap π H U).toImage
    (strictTransformOpenMap_toImage_over π H U) (strictTransformOpenMap_toImage_opensRange π H U)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Integral.StrictTransform.Construction
