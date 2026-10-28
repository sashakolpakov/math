import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruencePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.EtalePullback

/-! # Carrier Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CarrierBaseChange.Construction

noncomputable section

/-! Canonical actual maps on independently named pulled-back closed carriers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def idealSheafCarrierMapTo {X Y : Scheme.{u}} (H : X.IdealSheafData) (K : Y.IdealSheafData)
    (j : Y ⟶ X) (he : H.comap j = K) : K.subscheme ⟶ H.subscheme := by
  subst K
  exact (H.comapIso j).hom ≫ pullback.snd j H.subschemeι

theorem idealSheafCarrierMapTo_over {X Y : Scheme.{u}} (H : X.IdealSheafData) (K : Y.IdealSheafData)
    (j : Y ⟶ X) (he : H.comap j = K) :
    idealSheafCarrierMapTo H K j he ≫ H.subschemeι = K.subschemeι ≫ j := by
  subst K
  change ((H.comapIso j).hom ≫ pullback.snd j H.subschemeι) ≫ H.subschemeι = _
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, H.comapIso_hom_fst]

theorem idealSheafCarrierMapTo_isPullback {X Y : Scheme.{u}} (H : X.IdealSheafData) (K : Y.IdealSheafData)
    (j : Y ⟶ X) (he : H.comap j = K) :
    IsPullback (idealSheafCarrierMapTo H K j he) K.subschemeι H.subschemeι j := by
  subst K
  apply IsPullback.flip
  apply IsPullback.of_iso_pullback ⟨(idealSheafCarrierMapTo_over H (H.comap j) j rfl).symm⟩ (H.comapIso j)
  · exact H.comapIso_hom_fst j
  · rfl

instance idealSheafCarrierMapTo_etale {X Y : Scheme.{u}} (H : X.IdealSheafData) (K : Y.IdealSheafData)
    (j : Y ⟶ X) [Etale j] (he : H.comap j = K) : Etale (idealSheafCarrierMapTo H K j he) :=
  MorphismProperty.of_isPullback (P := @Etale) (idealSheafCarrierMapTo_isPullback H K j he).flip inferInstance

instance idealSheafCarrierMapTo_isOpenImmersion {X Y : Scheme.{u}} (H : X.IdealSheafData)
    (K : Y.IdealSheafData) (j : Y ⟶ X) [IsOpenImmersion j] (he : H.comap j = K) :
    IsOpenImmersion (idealSheafCarrierMapTo H K j he) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (idealSheafCarrierMapTo_isPullback H K j he).flip inferInstance

theorem idealSheaf_comap_subscheme_isIntegral {X Y : Scheme.{u}}
    (H : X.IdealSheafData) [IsIntegral H.subscheme] (j : Y ⟶ X) [IsOpenImmersion j]
    (x : Y) (hx : j x ∈ H.support) : IsIntegral (H.comap j).subscheme := by
  have hrange : x ∈ Set.range (H.comap j).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    exact hx
  obtain ⟨y, _⟩ := hrange
  let : Nonempty (H.comap j).subscheme := ⟨y⟩
  exact isIntegral_of_isOpenImmersion (idealSheafCarrierMapTo H (H.comap j) j rfl)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CarrierBaseChange.Construction
